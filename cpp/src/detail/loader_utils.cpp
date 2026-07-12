// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Loader-entry hardening helpers.
//
// Implementation of the path / size guards declared in `loader_utils.hpp`.
// Kept out-of-line because the ZIP central-directory walker uses `<fstream>`
// + binary IO; inlining into the header would force every translation unit
// that pulls `loader_utils.hpp` to see those headers.
//
#include "loader_utils.hpp"

#include <aletheia/error.hpp>
#include <aletheia/limits.hpp>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <expected>
#include <filesystem>
#include <fstream>
#include <ios>
#include <limits>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <system_error>
#include <utility>
#include <vector>

namespace aletheia::detail {

// ---------------------------------------------------------------------------
// Little-endian primitive readers — ZIP fields are always LE per APPNOTE 4.4.
// ---------------------------------------------------------------------------

static auto load_le16(const char* p) -> std::uint16_t {
    std::array<std::uint8_t, 2> b{};
    std::memcpy(b.data(), p, b.size());
    return static_cast<std::uint16_t>(static_cast<std::uint16_t>(b[0]) |
                                      static_cast<std::uint16_t>(b[1] << 8U));
}

static auto load_le32(const char* p) -> std::uint32_t {
    std::array<std::uint8_t, 4> b{};
    std::memcpy(b.data(), p, b.size());
    return static_cast<std::uint32_t>(b[0]) | (static_cast<std::uint32_t>(b[1]) << 8U) |
           (static_cast<std::uint32_t>(b[2]) << 16U) | (static_cast<std::uint32_t>(b[3]) << 24U);
}

// `vec.data() + off` would trip cppcoreguidelines-pro-bounds-pointer-arithmetic;
// `std::to_address(vec.begin() + off)` is the same address, arithmetic-free
// (canonical idiom — see `cpp/src/excel.cpp:sv_end_ptr`).  Buffers are
// `std::vector<char>` because `ifstream::read` takes `char*` and casting
// `std::byte*` would force a `reinterpret_cast` (banned by
// cppcoreguidelines-pro-type-reinterpret-cast).
static auto char_at(const std::vector<char>& v, std::size_t off) -> const char* {
    return std::to_address(v.begin() + static_cast<std::ptrdiff_t>(off));
}

// ---------------------------------------------------------------------------
// EOCD record — locates the ZIP central directory
// ---------------------------------------------------------------------------
//
// Format (APPNOTE 4.3.16): fixed 22-byte prefix + variable comment.
//   off  size  field
//     0   4    signature 0x06054b50
//     4   2    disk number
//     6   2    disk where CD starts
//     8   2    CD records on this disk
//    10   2    total CD records
//    12   4    CD size in bytes
//    16   4    CD offset from start of archive
//    20   2    comment length
//
// The comment can be up to 65535 bytes; the EOCD signature lives in the
// last (22 + comment_length) bytes of the file.  We scan the trailing
// 64 KiB + 22 bytes for the signature.

// The ZIP type + signature constants live in an anonymous namespace: the
// adopted clang-tidy style keeps file-local *types* (not functions) in an anon
// namespace, giving EOCD internal linkage so its common name can't ODR-clash
// across TUs.
namespace {

constexpr std::uint32_t k_eocd_sig = 0x06054b50;
constexpr std::uint32_t k_cd_entry_sig = 0x02014b50;
constexpr std::size_t k_eocd_min_size = 22;
constexpr std::size_t k_eocd_max_search = 65557; // 65535 + 22

struct EOCD {
    std::uint16_t total_entries;
    std::uint32_t cd_offset;
    std::uint32_t cd_size;
};

} // namespace

static auto find_eocd(std::ifstream& f, std::uintmax_t file_size) -> std::optional<EOCD> {
    if (file_size < k_eocd_min_size)
        return std::nullopt;

    const auto search_size =
        static_cast<std::size_t>(std::min<std::uintmax_t>(file_size, k_eocd_max_search));
    std::vector<char> tail(search_size);
    f.seekg(static_cast<std::streamoff>(file_size - search_size), std::ios::beg);
    f.read(tail.data(), static_cast<std::streamsize>(search_size));
    if (!f)
        return std::nullopt;

    // Scan backward from the latest possible EOCD start — first match wins.
    for (std::size_t i = search_size - k_eocd_min_size + 1; i-- > 0;) {
        if (load_le32(char_at(tail, i)) != k_eocd_sig)
            continue;
        const std::uint16_t disk_num = load_le16(char_at(tail, i + 4));
        const std::uint16_t cd_disk = load_le16(char_at(tail, i + 6));
        const std::uint16_t entries_this = load_le16(char_at(tail, i + 8));
        const std::uint16_t entries_total = load_le16(char_at(tail, i + 10));
        const std::uint32_t cd_size = load_le32(char_at(tail, i + 12));
        const std::uint32_t cd_off = load_le32(char_at(tail, i + 16));
        // Reject multi-disk / spanned archives — .xlsx is single-disk.
        if (disk_num != 0 || cd_disk != 0 || entries_this != entries_total)
            return std::nullopt;
        return EOCD{.total_entries = entries_total, .cd_offset = cd_off, .cd_size = cd_size};
    }
    return std::nullopt;
}

// ---------------------------------------------------------------------------
// Central-directory walker — sums uncompressed sizes
// ---------------------------------------------------------------------------
//
// CD entry layout (APPNOTE 4.3.12):
//   off  size  field
//     0   4    signature 0x02014b50
//    20   4    compressed size
//    24   4    uncompressed size
//    28   2    file name length
//    30   2    extra field length
//    32   2    file comment length
//    46   N    file name
//   46+N M    extra field
// 46+N+M K    file comment
//
// Total entry header = 46 + N + M + K bytes.

constexpr std::size_t k_cd_entry_min = 46;

static auto sum_uncompressed_sizes(std::ifstream& f, const EOCD& eocd)
    -> std::optional<std::uint64_t> {
    std::vector<char> cd(eocd.cd_size);
    f.seekg(eocd.cd_offset, std::ios::beg);
    f.read(cd.data(), static_cast<std::streamsize>(eocd.cd_size));
    if (!f)
        return std::nullopt;

    std::uint64_t total = 0;
    std::size_t off = 0;
    for (std::uint16_t i = 0; i < eocd.total_entries; ++i) {
        if (off + k_cd_entry_min > cd.size())
            return std::nullopt;
        if (load_le32(char_at(cd, off)) != k_cd_entry_sig)
            return std::nullopt;
        const std::uint32_t uncompressed = load_le32(char_at(cd, off + 24));
        const std::uint16_t name_len = load_le16(char_at(cd, off + 28));
        const std::uint16_t extra_len = load_le16(char_at(cd, off + 30));
        const std::uint16_t comment_len = load_le16(char_at(cd, off + 32));
        // Saturating add — refuse to silently wrap on a forged entry.
        if (uncompressed > std::numeric_limits<std::uint64_t>::max() - total)
            return std::nullopt;
        total += uncompressed;
        const std::size_t entry_size = k_cd_entry_min + name_len + extra_len + comment_len;
        if (off + entry_size > cd.size())
            return std::nullopt;
        off += entry_size;
    }
    return total;
}

// ===========================================================================
// Public helpers
// ===========================================================================

auto validate_loader_path(const std::filesystem::path& path, std::string_view kind)
    -> Result<void> {
    std::error_code ec;
    auto status = std::filesystem::symlink_status(path, ec);
    // A stat *failure* (EACCES on an unsearchable parent, ELOOP, ENAMETOOLONG,
    // or EMFILE/ENFILE/EIO under load) is NOT the same as a genuinely absent
    // file.  Reporting the former as "file not found" masks the real cause
    // (e.g. resource exhaustion during a heavily parallel run).  Key on the
    // errno VALUE, not merely on `ec` being set: libstdc++'s symlink_status
    // sets `ec` to ENOENT/ENOTDIR for a missing leaf or non-directory parent
    // component (it does NOT reliably clear `ec` for absence), so those two
    // codes still mean "not found".  Mirrors Go's errors.Is(err,
    // os.ErrNotExist), which likewise covers both ENOENT and ENOTDIR; matches
    // the sibling check_file_size_bound below (which surfaces ec.message()).
    if (ec) {
        if (ec == std::errc::no_such_file_or_directory || ec == std::errc::not_a_directory)
            return std::unexpected(AletheiaError{
                ErrorKind::Validation, std::string(kind) + " file not found: " + path.string()});
        return std::unexpected(AletheiaError{ErrorKind::Validation,
                                             "Could not stat " + std::string(kind) +
                                                 " file: " + path.string() + ": " + ec.message()});
    }
    if (!std::filesystem::exists(status))
        return std::unexpected(AletheiaError{
            ErrorKind::Validation, std::string(kind) + " file not found: " + path.string()});
    if (std::filesystem::is_symlink(status))
        return std::unexpected(AletheiaError{
            ErrorKind::Validation,
            std::string(kind) + " file is a symbolic link; refusing to load: " + path.string() +
                ".  Resolve and pass the real path."});
    if (!std::filesystem::is_regular_file(status))
        return std::unexpected(
            AletheiaError{ErrorKind::Validation,
                          std::string(kind) + " path is not a regular file: " + path.string()});
    return {};
}

// Build the structured InputBoundExceeded error shared by the file- and
// in-memory size checks.  `subject` ("File size" / "Input size") prefixes the
// message; the cross-binding bound_info shape (kind/observed/limit) is identical
// regardless of the input source.
static auto make_input_bound_error(std::uint64_t observed, std::string_view subject)
    -> AletheiaError {
    InputBoundExceededError info{.bound_kind = std::string{bound_kind_input_length_bytes},
                                 .observed = observed,
                                 .limit = max_dbc_text_bytes};
    return AletheiaError{ErrorKind::InputBoundExceeded,
                         std::string{subject} + " " + std::to_string(observed) + " exceeds limit " +
                             std::to_string(max_dbc_text_bytes) + " bytes",
                         ErrorCode::InputBoundExceeded, std::move(info)};
}

auto check_file_size_bound(const std::filesystem::path& path) -> Result<void> {
    std::error_code ec;
    const auto size = std::filesystem::file_size(path, ec);
    if (ec)
        return std::unexpected(AletheiaError{
            ErrorKind::Validation, "Could not stat file: " + path.string() + ": " + ec.message()});
    if (size > max_dbc_text_bytes)
        return std::unexpected(
            make_input_bound_error(static_cast<std::uint64_t>(size), "File size"));
    return {};
}

auto check_input_size_bound(std::uint64_t observed) -> Result<void> {
    if (observed > max_dbc_text_bytes)
        return std::unexpected(make_input_bound_error(observed, "Input size"));
    return {};
}

auto check_xlsx_uncompressed_bound(const std::filesystem::path& path) -> Result<void> {
    std::error_code ec;
    const auto file_size = std::filesystem::file_size(path, ec);
    if (ec)
        return std::unexpected(
            AletheiaError{ErrorKind::Validation, "Could not stat .xlsx archive: " + path.string()});

    std::ifstream f(path, std::ios::binary);
    if (!f)
        return std::unexpected(
            AletheiaError{ErrorKind::Validation, "Could not open .xlsx archive: " + path.string()});

    auto eocd = find_eocd(f, file_size);
    if (!eocd)
        return std::unexpected(AletheiaError{ErrorKind::Validation,
                                             "Not a valid .xlsx (ZIP) archive: " + path.string()});

    // Bound the central-directory allocation against the actual file size —
    // refuse a forged EOCD that asserts a multi-GiB CD inside a 50 KiB file.
    if (static_cast<std::uintmax_t>(eocd->cd_offset) > file_size ||
        static_cast<std::uintmax_t>(eocd->cd_size) > file_size ||
        static_cast<std::uintmax_t>(eocd->cd_offset) + eocd->cd_size > file_size)
        return std::unexpected(AletheiaError{
            ErrorKind::Validation,
            "Malformed central directory location in .xlsx archive: " + path.string()});

    auto total = sum_uncompressed_sizes(f, *eocd);
    if (!total)
        return std::unexpected(
            AletheiaError{ErrorKind::Validation,
                          "Malformed central directory in .xlsx archive: " + path.string()});

    if (*total > max_dbc_text_bytes) {
        InputBoundExceededError info{.bound_kind = std::string{bound_kind_input_length_bytes},
                                     .observed = *total,
                                     .limit = max_dbc_text_bytes};
        return std::unexpected(
            AletheiaError{ErrorKind::InputBoundExceeded,
                          ".xlsx uncompressed size " + std::to_string(*total) + " exceeds limit " +
                              std::to_string(max_dbc_text_bytes) + " bytes (ZIP-bomb defence)",
                          ErrorCode::InputBoundExceeded, std::move(info)});
    }
    return {};
}

auto validate_output_parent_dir(const std::filesystem::path& path) -> Result<void> {
    auto parent = path.parent_path();
    if (parent.empty())
        return {};
    std::error_code ec;
    if (!std::filesystem::is_directory(parent, ec) || ec)
        return std::unexpected(AletheiaError{
            ErrorKind::Validation, "Parent directory does not exist: " + parent.string()});
    return {};
}

} // namespace aletheia::detail
