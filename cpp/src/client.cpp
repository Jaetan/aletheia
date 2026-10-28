// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// AletheiaClient — orchestrates backend + JSON serialization/parsing.
#include <aletheia/client.hpp>
#include <aletheia/detail/cache_keys.hpp>
#include <aletheia/detail/checked.hpp>
#include <aletheia/limits.hpp>

#include "detail/client_checks.hpp"
#include "detail/json.hpp"

#include <algorithm>
#include <array>
#include <bit>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <expected>
#include <format>
#include <memory>
#include <optional>
#include <ranges>
#include <span>
#include <stop_token>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

// parse_extraction_bin uses std::memcpy reads in native byte order (per the
// canonical wire-format documentation in src/Aletheia/Main/Binary.agda,
// processExtractBin header comment).
// On a big-endian host the same memcpy would silently misinterpret the
// bytes; refuse to compile rather than ship an architecture-dependent ABI.
static_assert(std::endian::native == std::endian::little,
              "Aletheia FFI binary layout assumes little-endian native byte order; "
              "see src/Aletheia/Main/Binary.agda (processExtractBin) for the wire format.");

namespace aletheia::detail {

auto validate_payload(Dlc dlc, std::span<std::byte const> data) -> Result<void> {
    auto const expected = dlc_to_bytes(dlc);
    if (data.size() != expected)
        return std::unexpected(
            AletheiaError{ErrorKind::Validation,
                          std::format("payload length {} does not match DLC {} (expected {} bytes)",
                                      data.size(), dlc.value(), expected)});
    return {};
}

// Cancellation error helper. Constructed when a method's pre-FFI guard sees
// stop.stop_requested() and short-circuits before making the FFI call. The
// message includes the method name to mirror Go's
// `fmt.Errorf("method_name: %w", ctx.Err())` wrapping convention.
auto make_cancellation_error(std::string_view method) -> AletheiaError {
    return AletheiaError{ErrorKind::Cancellation,
                         std::format("{} cancelled by stop_token", method)};
}

} // namespace aletheia::detail

namespace aletheia {

using detail::make_cancellation_error;
using detail::validate_payload;

// The signal name a wire index denotes, or a placeholder for an index the
// DBC message does not have (a kernel/binding drift, surfaced rather than
// dropped).
static auto signal_name_at(std::vector<std::string> const& names, std::uint16_t idx) -> SignalName {
    return idx < names.size() ? SignalName{names.at(idx)}
                              : SignalName{std::format("signal_{}", idx)};
}

// Wire layout of the binary extraction buffer (src/Aletheia/Main/Binary.agda,
// processExtractBin header comment): a header of three u16 counts and one u32
// reason byte count, then one record per value, error, offset and absent
// signal.
constexpr std::size_t k_header_bytes = 10;
constexpr std::size_t k_value_record_bytes = 18;
constexpr std::size_t k_error_record_bytes = 3;
constexpr std::size_t k_offset_bytes = 4;
constexpr std::size_t k_absent_record_bytes = 2;

// Reads one integer at a byte offset the caller has bounds-checked, in the
// host's byte order, which is the order the kernel writes: see the wire-format
// header of processExtractBin in src/Aletheia/Main/Binary.agda.  Not the same
// operation as the ZIP walker's little-endian readers in loader_utils.cpp,
// whose byte order is fixed by that format rather than by the host; the two
// agree only because the assertion above forbids a big-endian build.
template<typename T>
static auto read_native(std::span<std::byte const> buf, std::size_t off) -> T {
    alignas(T) std::array<std::byte, sizeof(T)> raw{};
    std::ranges::copy(detail::subspan_at(buf, off, sizeof(T)), raw.begin());
    return std::bit_cast<T>(raw);
}

auto AletheiaClient::create(std::unique_ptr<IBackend> backend, Logger logger,
                            std::vector<CheckResult> default_checks) -> Result<AletheiaClient> {
    return backend->init()
        .and_then([](BackendState state) -> Result<BackendState> {
            if (!state)
                return std::unexpected(
                    AletheiaError{ErrorKind::Ffi, "backend init() returned null state"});
            return state;
        })
        .transform([&](BackendState state) {
            return AletheiaClient{std::move(backend), std::move(state), std::move(logger),
                                  std::move(default_checks)};
        });
}

auto AletheiaClient::open(ClientOptions options) -> Result<AletheiaClient> {
    auto const library = options.library.empty() ? find_ffi_library()
                                                 : Result<std::filesystem::path>{options.library};
    if (!library)
        return std::unexpected(detail::error_of(library));
    auto backend = options.rts_cores ? make_ffi_backend(library.value(), options.rts_cores.value())
                                     : make_ffi_backend(library.value());
    return std::move(backend).and_then([&options](std::unique_ptr<IBackend> opened) {
        return create(std::move(opened), std::move(options.logger),
                      std::move(options.default_checks));
    });
}

AletheiaClient::AletheiaClient(std::unique_ptr<IBackend> backend, BackendState state, Logger logger,
                               std::vector<CheckResult> default_checks)
    : backend_(std::move(backend))
    , state_(std::move(state))
    , logger_(std::move(logger))
    , default_checks_(std::move(default_checks)) {
    // Parity with the `rts.cores_mismatch` event of Go (go/aletheia/ffi.go) and
    // Python (python/aletheia/client/_ffi.py), both of which carry
    // `active_cores` and `requested_cores` integer fields.
    if (auto const rts = backend_->rts_mismatch_info(); rts) {
        auto const active = static_cast<std::int64_t>(rts.value().first);
        auto const requested = static_cast<std::int64_t>(rts.value().second);
        logger_.warn("rts.cores_mismatch",
                     {{"active_cores", active}, {"requested_cores", requested}});
    }
}

// The state handle releases itself, so the destructor has nothing left to do.
// Destruction order is what carries the policy: state_ is declared after
// backend_, so it closes through a backend that is still alive.
AletheiaClient::~AletheiaClient() = default;

AletheiaClient::AletheiaClient(AletheiaClient&& other) noexcept
    : backend_(std::move(other.backend_))
    , state_(std::move(other.state_))
    , logger_(std::move(other.logger_))
    , default_checks_(std::move(other.default_checks_))
    , diags_(std::move(other.diags_))
    , cache_(std::move(other.cache_))
    , last_frames_(std::move(other.last_frames_))
    , signal_index_(std::move(other.signal_index_))
    , signal_names_(std::move(other.signal_names_)) {
}

AletheiaClient& AletheiaClient::operator=(AletheiaClient&& other) noexcept {
    if (this != &other) {
        // The handle is assigned before the backend it closes through, so the
        // state this client held is released while its own backend is alive.
        state_ = std::move(other.state_);
        backend_ = std::move(other.backend_);
        logger_ = std::move(other.logger_);
        default_checks_ = std::move(other.default_checks_);
        diags_ = std::move(other.diags_);
        cache_ = std::move(other.cache_);
        last_frames_ = std::move(other.last_frames_);
        signal_index_ = std::move(other.signal_index_);
        signal_names_ = std::move(other.signal_names_);
    }
    return *this;
}

// ---------------------------------------------------------------------------
// DBC
// ---------------------------------------------------------------------------

// Refresh signal name → index cache from a parsed DBC.  Shared between
// parse_dbc (DBC-as-JSON input) and parse_dbc_text (raw DBC text input).
void AletheiaClient::populate_signal_lookup(DbcDefinition const& dbc) {
    signal_index_.clear();
    signal_names_.clear();
    for (auto const& msg : dbc.messages) {
        auto const id_value = can_id_value(msg.id);
        auto const is_extended = can_id_is_extended(msg.id);
        std::vector<std::string> names;
        for (auto const [i, signal] : std::views::enumerate(msg.signals)) {
            signal_index_.emplace(detail::SignalKey{.id_value = id_value,
                                                    .is_extended = is_extended,
                                                    .signal_name = signal.name.get()},
                                  static_cast<std::uint32_t>(i));
            names.emplace_back(signal.name.get());
        }
        signal_names_.emplace(detail::MessageKey{id_value, is_extended}, std::move(names));
    }
}

auto AletheiaClient::run_command(Result<std::string> const& command) -> Result<std::string> {
    return command.and_then(
        [this](std::string const& text) { return backend_->process(state_, text); });
}

auto AletheiaClient::parse_dbc(std::stop_token stop, DbcDefinition const& dbc)
    -> Result<ParsedDBC> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("parse_dbc"));
    auto result = run_command(detail::serialize_parse_dbc(dbc)).and_then(detail::parse_parsed_dbc);
    if (result.has_value()) {
        populate_signal_lookup(result.value().dbc);
        logger_.info(
            "dbc.parsed",
            {{"messages", static_cast<std::uint64_t>(result.value().dbc.messages.size())}});
    }
    return result;
}

auto AletheiaClient::parse_dbc_text(std::stop_token stop, std::string_view text)
    -> Result<ParsedDBC> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("parse_dbc_text"));
    // Defense-in-depth (cross-binding parity):
    // reject DBC text inputs longer than max_dbc_text_bytes before wrapping
    // them in a JSON command.  The outer max_json_bytes cap in
    // FfiBackend::process covers the wrapped command separately; the
    // additional inner cap matches the Agda kernel's two-layer enforcement
    // in handleParseDBCText.
    if (text.size() > max_dbc_text_bytes) {
        return std::unexpected(
            AletheiaError{ErrorKind::InputBoundExceeded,
                          "input length (bytes) " + std::to_string(text.size()) +
                              " exceeds limit " + std::to_string(max_dbc_text_bytes),
                          ErrorCode::InputBoundExceeded,
                          InputBoundExceededError{
                              .bound_kind = std::string{bound_kind_input_length_bytes},
                              .observed = static_cast<std::uint64_t>(text.size()),
                              .limit = max_dbc_text_bytes,
                          }});
    }
    auto result =
        run_command(detail::serialize_parse_dbc_text(text)).and_then(detail::parse_parsed_dbc);
    if (result.has_value()) {
        populate_signal_lookup(result.value().dbc);
        logger_.info(
            "dbc.parsed",
            {{"messages", static_cast<std::uint64_t>(result.value().dbc.messages.size())}});
    }
    return result;
}

auto AletheiaClient::validate_dbc(std::stop_token stop, DbcDefinition const& dbc)
    -> Result<ValidationResult> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("validate_dbc"));
    return run_command(detail::serialize_validate_dbc(dbc)).and_then(detail::parse_validation);
}

auto AletheiaClient::format_dbc(std::stop_token stop) -> Result<DbcDefinition> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("format_dbc"));
    return backend_->format_dbc_binary(state_).and_then(detail::parse_dbc_response);
}

auto AletheiaClient::format_dbc_text(std::stop_token stop, DbcDefinition const& dbc)
    -> Result<DbcText> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("format_dbc_text"));
    return run_command(detail::serialize_format_dbc_text(dbc))
        .and_then(detail::parse_dbc_text_response);
}

// ---------------------------------------------------------------------------
// Signals
// ---------------------------------------------------------------------------

// Constructs a SignalValue from a wire-extracted (idx, num, den) triple.
// Centralizes the den-positive normalization required for cross-binding
// wire symmetry and keeps `parse_extraction_bin`
// under the clang-tidy readability-function-size threshold.
static auto wire_signal_value(std::uint16_t idx, std::int64_t num, std::int64_t den,
                              std::vector<std::string> const& names) -> Result<SignalValue> {
    auto name = signal_name_at(names, idx);
    if (den == 0)
        return std::unexpected(AletheiaError{
            ErrorKind::Protocol,
            std::format("Zero denominator in extraction value for {}", std::string_view{name})});
    auto const rat_or_err = Rational::make(num, den);
    if (!rat_or_err)
        return std::unexpected(
            AletheiaError{ErrorKind::Protocol,
                          std::format("Invalid rational in extraction value for {}: num={}, den={}",
                                      std::string_view{name}, num, den)});
    return SignalValue{.name = std::move(name), .value = PhysicalValue{rat_or_err.value()}};
}

// True iff `bytes` is well-formed UTF-8 (RFC 3629): continuation bytes in
// place, no overlong encodings, no surrogate code points, nothing above
// U+10FFFF, no truncated sequences.  Wire reasons are validated per reason
// slice — offsets are byte offsets, so a slice boundary that splits a
// multi-byte sequence makes that slice invalid and is a protocol error.
static auto is_valid_utf8(std::span<std::byte const> bytes) -> bool {
    // Minimum code point per sequence length — anything below is overlong.
    constexpr std::array<std::uint32_t, 5> min_cp = {0, 0, 0x80, 0x800, 0x10000};
    // A cursor, because a sequence is as many bytes as its lead byte says:
    // the step is not a constant and the remainder is what the next step
    // reads, so the span carries the position instead of an index compared
    // against a length.
    while (!bytes.empty()) {
        auto const b0 = static_cast<std::uint8_t>(bytes.front());
        if (b0 < 0x80) {
            bytes = detail::subspan_at(bytes, 1);
            continue;
        }
        // The lead byte names the sequence length and the bits it carries, or
        // is a lone continuation or invalid lead byte, which names nothing.
        auto const lead = [b0] -> std::optional<std::pair<std::size_t, std::uint32_t>> {
            if ((b0 & 0xE0U) == 0xC0)
                return std::pair{std::size_t{2}, std::uint32_t{b0 & 0x1FU}};
            if ((b0 & 0xF0U) == 0xE0)
                return std::pair{std::size_t{3}, std::uint32_t{b0 & 0x0FU}};
            if ((b0 & 0xF8U) == 0xF0)
                return std::pair{std::size_t{4}, std::uint32_t{b0 & 0x07U}};
            return std::nullopt;
        }();
        if (!lead)
            return false;
        auto [len, cp] = lead.value();
        if (len > bytes.size())
            return false;
        for (auto const byte : detail::subspan_at(detail::subspan_at(bytes, 0, len), 1)) {
            auto const bk = static_cast<std::uint8_t>(byte);
            if ((bk & 0xC0U) != 0x80)
                return false;
            cp = (cp << 6U) | (bk & 0x3FU);
        }
        if (cp < min_cp.at(len) || cp > 0x10FFFF || (cp >= 0xD800 && cp <= 0xDFFF))
            return false;
        bytes = detail::subspan_at(bytes, len);
    }
    return true;
}

// Decodes the Errors + Offsets + Reasons wire segments starting at
// `errors_off` (layout: src/Aletheia/Main/Binary.agda, processExtractBin
// header comment).  Each error's reason is the kernel-minted detailed string
// carried on the wire — byte-identical to what the JSON path surfaces for
// the same error.  The u8 error code is transported for machine consumption
// but is not part of the public result: the JSON path has no code field and
// binary/JSON parity of the public surface is a repo invariant, so the code
// is skipped here and unknown codes are not rejected (the reason is
// authoritative).
static auto wire_signal_errors(std::span<std::byte const> buf, std::size_t errors_off,
                               std::uint16_t nerrs, std::uint32_t reason_bytes,
                               std::vector<std::string> const& names)
    -> Result<std::vector<SignalError>> {
    auto const offsets_off = errors_off + (std::size_t{nerrs} * k_error_record_bytes);
    auto const reasons_off = offsets_off + ((std::size_t{nerrs} + 1) * k_offset_bytes);
    // Each segment is a run of fixed-size records, so it is read as the
    // records themselves: the count and the slicing then agree by
    // construction, and the segments lie inside the buffer by the caller's
    // exact-size check.  The offset table holds one more entry than there are
    // records, the end of the last reason.
    auto const records =
        detail::subspan_at(buf, errors_off, std::size_t{nerrs} * k_error_record_bytes) |
        std::views::chunk(k_error_record_bytes);
    auto const offsets =
        detail::subspan_at(buf, offsets_off, (std::size_t{nerrs} + 1) * k_offset_bytes) |
        std::views::chunk(k_offset_bytes) | std::views::transform([](auto const entry) {
            return read_native<std::uint32_t>(std::span<std::byte const>{entry}, 0);
        });
    // Each reason is the span between two neighbouring offsets, so the
    // table is read two entries at a time, which is also what says whether it
    // is monotone.
    auto const bounds = offsets | std::views::slide(2);

    // Offset-table invariants, all three verified before any reason is
    // sliced out: off[0] == 0, monotone non-decreasing,
    // off[nerrs] == reason_bytes.
    if (offsets.front() != 0)
        return std::unexpected(AletheiaError{
            ErrorKind::Protocol,
            std::format("Malformed extraction reason offsets: first offset is {}, must be 0",
                        offsets.front())});
    for (auto const [i, bound] : std::views::enumerate(bounds)) {
        if (bound.front() > bound.back())
            return std::unexpected(AletheiaError{
                ErrorKind::Protocol,
                std::format("Malformed extraction reason offsets: offset {} decreases", i + 1)});
    }
    if (offsets.back() != reason_bytes)
        return std::unexpected(AletheiaError{
            ErrorKind::Protocol,
            std::format("Malformed extraction reason offsets: last offset {} != reason bytes {}",
                        offsets.back(), reason_bytes)});

    std::vector<SignalError> errors;
    errors.reserve(nerrs);
    for (auto const [record, bound] : std::views::zip(records, bounds)) {
        auto name = signal_name_at(
            names, read_native<std::uint16_t>(std::span<std::byte const>{record}, 0));
        auto const slice =
            detail::subspan_at(buf, reasons_off + bound.front(), bound.back() - bound.front());
        if (!is_valid_utf8(slice))
            return std::unexpected(AletheiaError{
                ErrorKind::Protocol,
                std::format("Invalid UTF-8 in extraction reason for {}", std::string_view{name})});
        std::string reason(slice.size(), '\0');
        std::ranges::transform(slice, reason.begin(),
                               [](std::byte b) { return static_cast<char>(b); });
        errors.emplace_back(std::move(name), std::move(reason));
    }
    return errors;
}

// Parses the binary extraction layout emitted by `aletheia_extract_signals_bin`.
// Layout and byte order (native; little-endian on all supported platforms) are
// documented in src/Aletheia/Main/Binary.agda (processExtractBin header
// comment): Header (3×u16 counts + u32 reasonBytes) + Values (×18B) +
// Errors (×3B) + Offsets ((nErrors+1)×u32, always present) + Reasons (UTF-8
// blob) + Absent (×2B).  Cross-arch deployment would require byteswapping on
// the reader side.
static auto parse_extraction_bin(std::span<std::byte const> buf,
                                 std::vector<std::string> const& names)
    -> Result<ExtractionResult> {
    auto const read_u16 = [&](std::size_t off) { return read_native<std::uint16_t>(buf, off); };
    auto const read_u32 = [&](std::size_t off) { return read_native<std::uint32_t>(buf, off); };

    if (buf.size() < k_header_bytes)
        return std::unexpected(AletheiaError{
            ErrorKind::Protocol,
            std::format("Truncated extraction buffer: {} bytes, need >= {} for the header",
                        buf.size(), k_header_bytes)});
    auto const nvals = read_u16(0);
    auto const nerrs = read_u16(2);
    auto const nabss = read_u16(4);
    auto const reason_bytes = read_u32(6);
    // Counts are u16 and reason_bytes is u32, so the max expected_size is
    // ~4 GiB — far below SIZE_MAX on any supported (64-bit) platform.
    auto const expected_size =
        k_header_bytes + (std::size_t{nvals} * k_value_record_bytes) +
        (std::size_t{nerrs} * k_error_record_bytes) + ((std::size_t{nerrs} + 1) * k_offset_bytes) +
        std::size_t{reason_bytes} + (std::size_t{nabss} * k_absent_record_bytes);
    // Exact-size check: too short is truncation, too long is trailing bytes.
    if (buf.size() != expected_size)
        return std::unexpected(AletheiaError{
            ErrorKind::Protocol,
            std::format("Extraction buffer size mismatch: {} bytes, expected exactly {}",
                        buf.size(), expected_size)});
    auto off = k_header_bytes;

    ExtractionResult result;
    result.values.reserve(nvals);
    // A run of fixed-size records, read as the records: the stride is the
    // view's and not an addition this loop repeats.
    for (auto const entry :
         detail::subspan_at(buf, off, std::size_t{nvals} * k_value_record_bytes) |
             std::views::chunk(k_value_record_bytes)) {
        std::span<std::byte const> const record{entry};
        auto sv = wire_signal_value(read_native<std::uint16_t>(record, 0),
                                    read_native<std::int64_t>(record, 2),
                                    read_native<std::int64_t>(record, 10), names);
        if (!sv)
            return std::unexpected(detail::error_of(sv));
        result.values.push_back(std::move(sv).value());
    }
    off += std::size_t{nvals} * k_value_record_bytes;
    // Errors + Offsets + Reasons — all three segments lie within the buffer
    // by the exact-size check above; the helper verifies the offset-table
    // invariants and validates each reason slice as UTF-8.
    auto errors = wire_signal_errors(buf, off, nerrs, reason_bytes, names);
    if (!errors)
        return std::unexpected(detail::error_of(errors));
    result.errors = std::move(errors).value();
    off += (std::size_t{nerrs} * k_error_record_bytes) +
           ((std::size_t{nerrs} + 1) * k_offset_bytes) + std::size_t{reason_bytes};
    result.absent.reserve(nabss);
    for (auto const entry :
         detail::subspan_at(buf, off, std::size_t{nabss} * k_absent_record_bytes) |
             std::views::chunk(k_absent_record_bytes)) {
        result.absent.push_back(signal_name_at(
            names, read_native<std::uint16_t>(std::span<std::byte const>{entry}, 0)));
    }
    return result;
}

auto AletheiaClient::extract_signals(std::stop_token stop, CanId id, Dlc dlc,
                                     std::span<std::byte const> data) -> Result<ExtractionResult> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("extract_signals"));
    if (auto const v = validate_payload(dlc, data); !v.has_value())
        return std::unexpected(detail::error_of(v));

    // Use binary path when signal name cache is populated. Only
    // ErrorKind::BinaryUnsupported (e.g. MockBackend) triggers the JSON
    // fallback — any other error (decode / truncation / real FFI failure)
    // propagates, matching Go's ErrBinaryPathUnsupported contract.
    auto const id_value = can_id_value(id);
    auto const is_extended = can_id_is_extended(id);
    auto const names_it = signal_names_.find(detail::MessageKey{id_value, is_extended});
    if (names_it != signal_names_.end()) {
        auto const buf = backend_->extract_signals_bin(state_, id, dlc, data);
        if (buf)
            return parse_extraction_bin(buf.value(), names_it->second);
        if (detail::error_of(buf).kind() != ErrorKind::BinaryUnsupported)
            return std::unexpected(detail::error_of(buf));
        // BinaryUnsupported: fall through to JSON path.
    }

    // Fallback: JSON path.
    return backend_->extract_signals_binary(state_, id, dlc, data)
        .and_then(detail::parse_extraction);
}

auto AletheiaClient::ResolvedSignals::injection() const -> Result<SignalInjection> {
    return SignalInjection::create(indices, numerators, denominators);
}

auto AletheiaClient::resolve_signals(std::string_view method, CanId id,
                                     std::span<SignalValue const> signals)
    -> Result<ResolvedSignals> {
    if (signal_index_.empty())
        return std::unexpected(AletheiaError{
            ErrorKind::State, std::format("{}: no DBC loaded (call parse_dbc first)", method)});
    auto const id_value = can_id_value(id);
    auto const is_extended = can_id_is_extended(id);

    // Distinguish "this CAN ID has no DBC message" from "this message lacks this
    // signal": without this guard a missing message collapses into the per-signal
    // "signal not found" error below (misleading), and a zero-signal call would
    // silently succeed.  Mirrors Go (resolveSignalIndices) and Python
    // (_resolve_signal_indices), which guard message-existence before iterating.
    if (!signal_names_.contains(detail::MessageKey{id_value, is_extended})) {
        return std::unexpected(AletheiaError{
            ErrorKind::Validation,
            std::format("no DBC message for CAN ID {} (extended={})", id_value, is_extended)});
    }

    // Sized once from the input, so the three arrays are the block the FFI
    // reads and not a growth that could diverge from it.
    ResolvedSignals resolved{.indices = std::vector<std::uint32_t>(signals.size()),
                             .numerators = std::vector<std::int64_t>(signals.size()),
                             .denominators = std::vector<std::int64_t>(signals.size())};
    for (auto const& [sv, index, numerator, denominator] :
         std::views::zip(signals, resolved.indices, resolved.numerators, resolved.denominators)) {
        auto const it = signal_index_.find(detail::SignalKey{
            .id_value = id_value, .is_extended = is_extended, .signal_name = sv.name.get()});
        if (it == signal_index_.end()) {
            return std::unexpected(AletheiaError{
                ErrorKind::Validation, std::format("signal '{}' not found in DBC for CAN ID {}",
                                                   std::string_view{sv.name}, id_value)});
        }
        index = it->second;
        auto const& r = sv.value.get();
        numerator = r.numerator();
        denominator = r.denominator();
    }
    return resolved;
}

auto AletheiaClient::build_frame(std::stop_token stop, CanId id, Dlc dlc,
                                 std::span<SignalValue const> signals) -> Result<FramePayload> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("build_frame"));
    auto const resolved = resolve_signals("build_frame", id, signals);
    if (!resolved) {
        return std::unexpected(detail::error_of(resolved));
    }
    auto const inj = resolved.value().injection();
    if (!inj)
        return std::unexpected(detail::error_of(inj));
    return backend_->build_frame_bin(state_, id, dlc, inj.value(), dlc_to_bytes(dlc));
}

auto AletheiaClient::update_frame(std::stop_token stop, CanId id, Dlc dlc,
                                  std::span<std::byte const> data,
                                  std::span<SignalValue const> signals) -> Result<FramePayload> {
    if (stop.stop_requested()) [[unlikely]]
        return std::unexpected(make_cancellation_error("update_frame"));
    if (auto const v = validate_payload(dlc, data); !v.has_value()) {
        return std::unexpected(detail::error_of(v));
    }
    auto const resolved = resolve_signals("update_frame", id, signals);
    if (!resolved) {
        return std::unexpected(detail::error_of(resolved));
    }
    auto const inj = resolved.value().injection();
    if (!inj)
        return std::unexpected(detail::error_of(inj));
    return backend_->update_frame_bin(state_, id, dlc, data, inj.value(), dlc_to_bytes(dlc));
}

auto AletheiaClient::extract_signals_internal(CanId id, Dlc dlc, std::span<std::byte const> data,
                                              std::uint32_t id_value, bool is_extended)
    -> std::optional<ExtractionResult> {
    // Use binary path when signal name cache is populated. Mirrors the
    // ErrorKind::BinaryUnsupported fallback contract in extract_signals:
    // only that kind triggers the JSON fallback; any other error is a real
    // failure (decode / truncation / genuine FFI error) logged + surfaced
    // as std::nullopt.
    auto const names_it = signal_names_.find(detail::MessageKey{id_value, is_extended});
    if (names_it != signal_names_.end()) {
        auto const buf = backend_->extract_signals_bin(state_, id, dlc, data);
        if (buf) {
            auto bin_result = parse_extraction_bin(buf.value(), names_it->second);
            if (!bin_result) {
                logger_.warn("extraction.parse_failed",
                             {{"canId", static_cast<std::uint64_t>(id_value)},
                              {"error", detail::error_of(bin_result).message()}});
                return std::nullopt;
            }
            return std::move(bin_result).value();
        }
        if (detail::error_of(buf).kind() != ErrorKind::BinaryUnsupported) {
            logger_.warn("extraction.process_failed",
                         {{"canId", static_cast<std::uint64_t>(id_value)},
                          {"error", detail::error_of(buf).message()}});
            return std::nullopt;
        }
        // BinaryUnsupported: fall through to JSON path.
    }

    // Fallback: JSON path.
    //
    // Matches the binary path above: log and return nullopt for any failure
    // other than BinaryUnsupported.  The log warning carries the message but no
    // kind field, to preserve cross-binding parity with Python and Go's
    // `extraction.process_failed` event signature.
    auto const resp = backend_->extract_signals_binary(state_, id, dlc, data);
    if (!resp) {
        logger_.warn("extraction.process_failed", {{"canId", static_cast<std::uint64_t>(id_value)},
                                                   {"error", detail::error_of(resp).message()}});
        return std::nullopt;
    }
    auto result = detail::parse_extraction(resp.value());
    if (!result.has_value()) {
        logger_.warn("extraction.parse_failed", {{"canId", static_cast<std::uint64_t>(id_value)},
                                                 {"error", detail::error_of(result).message()}});
        return std::nullopt;
    }
    return std::move(result).value();
}

} // namespace aletheia
