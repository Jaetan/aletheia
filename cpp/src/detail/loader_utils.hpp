// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// Shared condition dispatch logic for YAML and Excel check loaders, plus
// path / size hardening helpers used at every loader entry point per
// AGENTS.md universal rule "Adversarial-input bounds at parser surfaces".
//
// Both loaders accept the same set of condition keywords and dispatch them
// through the same Check API builders.  This header defines the keyword
// constants and dispatch helpers so the two loaders stay in sync.
//
#pragma once

#include <aletheia/check.hpp>
#include <aletheia/error.hpp>
#include <aletheia/types.hpp>

#include <array>
#include <chrono>
#include <cstdint>
#include <filesystem>
#include <ios>
#include <istream>
#include <map>
#include <optional>
#include <span>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>

namespace aletheia::detail {

// ---------------------------------------------------------------------------
// Loader-entry hardening helpers
// ---------------------------------------------------------------------------

/// Validate a loader input path: must exist, be a regular file, and NOT
/// be a symbolic link.  The symlink rejection is deliberately strict —
/// canonicalisation would FOLLOW the link, defeating the check.  A
/// caller passing a legitimate symlink must resolve it before invoking
/// the loader.  Mirrors the lstat-then-reject pattern of the Python loader
/// helpers (`python/aletheia/_loader_utils.py`).
///
/// `kind` ("Excel" / "YAML") names the loader in the error message.
///
/// TOCTOU note: there is a small window between `is_symlink` here and
/// the eventual file-open in OpenXLSX / yaml-cpp.  Strict closure
/// requires fd-based plumbing (`open(O_NOFOLLOW)` + `fstat`) into the
/// vendored libraries' APIs which they don't expose.  The residual
/// risk requires attacker write access on the parent directory.
///
/// Returns `Result<void>`:
///   - Path doesn't exist           → `ErrorKind::Validation`
///   - Path is a symbolic link      → `ErrorKind::Validation`
///   - Path is not a regular file   → `ErrorKind::Validation`
[[nodiscard]] auto validate_loader_path(const std::filesystem::path& path, std::string_view kind)
    -> Result<void>;

/// Reject if the file's raw byte count exceeds `max_dbc_text_bytes`.
/// Defense-in-depth size cap mirroring Python's `check_dbc_text_size_bound`
/// (python/aletheia/client/_types.py).  Returns `ErrorKind::InputBoundExceeded`
/// with structured `bound_info = {kind="input_length_bytes",
/// observed=file_size, limit=max_dbc_text_bytes}` so the cross-binding
/// `InputBoundExceededError` shape (Python / Go / C++) stays identical.
[[nodiscard]] auto check_file_size_bound(const std::filesystem::path& path) -> Result<void>;

/// Reject if an in-memory input's byte length exceeds `max_dbc_text_bytes`.
/// The inline-string analogue of `check_file_size_bound`, for loaders that
/// receive their input as a `std::string`/`std::string_view` (e.g. the inline
/// YAML loader) rather than a file path.  Same structured
/// `InputBoundExceededError` shape, so the cross-binding trust boundary holds
/// on inline input too (Go / Rust bound their inline loaders likewise).
[[nodiscard]] auto check_input_size_bound(std::uint64_t observed) -> Result<void>;

/// Walk the ZIP archive's central directory and reject when the sum of
/// uncompressed entry sizes exceeds `max_dbc_text_bytes` — defense
/// against ZIP bombs where a small archive (e.g. ~50 KiB) decompresses
/// to multiple GiB of XML, exhausting heap inside OpenXLSX.  Mirrors Python's
/// `_check_xlsx_uncompressed_bound` (python/aletheia/excel_loader.py).
///
/// The implementation is a minimal, defensive central-directory parser;
/// no third-party ZIP library is pulled in.  Rationale: we already require
/// the file to fit in `max_dbc_text_bytes` (so ZIP64 is unnecessary),
/// reject every multi-disk / unknown structure outright, and depend only
/// on `<fstream>`.
///
/// Errors:
///   - File too small to be a ZIP / EOCD missing → `ErrorKind::Validation`
///   - Multi-disk / spanning archive             → `ErrorKind::Validation`
///   - Sum of uncompressed sizes overflows / exceeds bound
///                                                → `ErrorKind::InputBoundExceeded`
[[nodiscard]] auto check_xlsx_uncompressed_bound(const std::filesystem::path& path) -> Result<void>;

// Fills `out` from the stream at `offset`, and says whether it could: a read
// the stream cut short, or refused, is false, and `out` then holds bytes the
// caller must not read. The archive walker's two positioned reads share it.
[[nodiscard]] auto read_exactly(std::istream& in, std::streamoff offset, std::span<char> out)
    -> bool;

// ---------------------------------------------------------------------------
// Output-path hardening (`create_excel_template`)
// ---------------------------------------------------------------------------

/// Validate that the parent directory of `path` exists and is itself a
/// directory (not a file, not missing).  Empty parent (i.e. cwd-relative)
/// is allowed.  `ErrorKind::Validation` on failure.
[[nodiscard]] auto validate_output_parent_dir(const std::filesystem::path& path) -> Result<void>;

// ---------------------------------------------------------------------------
// Condition keywords, as both loaders spell them
// ---------------------------------------------------------------------------

inline constexpr std::string_view k_never_exceeds = "never_exceeds";
inline constexpr std::string_view k_never_below = "never_below";
inline constexpr std::string_view k_never_equals = "never_equals";
inline constexpr std::string_view k_stays_between = "stays_between";
inline constexpr std::string_view k_settles_between = "settles_between";
inline constexpr std::string_view k_equals = "equals";
inline constexpr std::string_view k_exceeds = "exceeds";
inline constexpr std::string_view k_drops_below = "drops_below";

// ---------------------------------------------------------------------------
// Condition dispatch helpers
// ---------------------------------------------------------------------------

/// Apply a simple single-signal, single-value condition (never_exceeds/below/equals).
[[nodiscard]] inline auto dispatch_simple(std::string_view signal, std::string_view condition,
                                          PhysicalValue value) -> CheckResult {
    if (condition == k_never_exceeds)
        return check::signal(std::string{signal}).never_exceeds(value);
    if (condition == k_never_below)
        return check::signal(std::string{signal}).never_below(value);
    if (condition == k_never_equals)
        return check::signal(std::string{signal}).never_equals(value);
    // The caller holds the word to the vocabulary first, so this is the path a
    // word added to the vocabulary and to no builder takes. It is a runtime_error
    // because that is what both loaders catch and turn into a typed refusal; a
    // logic_error would escape them and end the process.
    throw std::runtime_error("Unknown simple condition: " + std::string{condition});
}

/// Apply a when-condition to a WhenSignal builder.
[[nodiscard]] inline auto dispatch_when(WhenSignal const& builder, std::string_view condition,
                                        PhysicalValue value) -> WhenCondition {
    if (condition == k_exceeds)
        return builder.exceeds(value);
    if (condition == k_equals)
        return builder.equals(value);
    if (condition == k_drops_below)
        return builder.drops_below(value);
    throw std::runtime_error("Unknown when condition: " + std::string{condition});
}

/// The values a loader read for an obligation, keyed by the slot each fills:
/// `value` for the one-value obligations, `lo` and `hi` for the range.
using ThenSlotValues = std::map<std::string_view, PhysicalValue>;

/// Build the obligation a word names, from the slots the table says it reads.
/// The loader hands over the slots its obligation reads and no others, so
/// there is no filler for a slot nobody looks at: a slot this reads and the
/// loader did not pass is refused by name rather than read as zero. A word
/// outside the table is refused here rather than built as whichever branch
/// came last, which is what both loaders used to do.
[[nodiscard]] inline auto dispatch_then(const ThenSignal& builder, std::string_view condition,
                                        const ThenSlotValues& slots,
                                        std::chrono::milliseconds within) -> CheckResult {
    auto const slot = [&](std::string_view name) -> PhysicalValue {
        auto const found = slots.find(name);
        if (found == slots.end())
            throw std::runtime_error("then condition '" + std::string{condition} +
                                     "' reads slot '" + std::string{name} +
                                     "', which the loader did not pass");
        return found->second;
    };
    if (condition == k_equals)
        return builder.equals(slot("value")).within(within);
    if (condition == k_exceeds)
        return builder.exceeds(slot("value")).within(within);
    if (condition == k_stays_between)
        return builder.stays_between(slot("lo"), slot("hi")).within(within);
    throw std::runtime_error("Unknown then condition: " + std::string{condition});
}

// ---------------------------------------------------------------------------
// Condition keyword predicates
// ---------------------------------------------------------------------------

[[nodiscard]] inline auto is_simple_value_condition(std::string_view c) -> bool {
    return c == k_never_exceeds || c == k_never_below || c == k_never_equals;
}

[[nodiscard]] inline auto is_simple_range_condition(std::string_view c) -> bool {
    return c == k_stays_between;
}

[[nodiscard]] inline auto is_simple_settles_condition(std::string_view c) -> bool {
    return c == k_settles_between;
}

[[nodiscard]] inline auto is_simple_condition(std::string_view c) -> bool {
    return is_simple_value_condition(c) || is_simple_range_condition(c) ||
           is_simple_settles_condition(c) || c == k_equals;
}

[[nodiscard]] inline auto is_when_condition(std::string_view c) -> bool {
    return c == k_exceeds || c == k_equals || c == k_drops_below;
}

/// The value slots an obligation reads: one value, or a pair of bounds.
enum class ThenSlots : std::uint8_t { Value, Range };

/// Which slots each obligation reads, written once. A loader asks this rather
/// than deciding again, because a loader that decides does so with a trailing
/// branch: a word this table gained and that branch did not was built as
/// whatever the branch happened to be, which was the range obligation in both
/// loaders of both bindings. The set a loader accepts is this table's keys, so
/// an obligation cannot be accepted and unclassified.
inline constexpr std::array<std::pair<std::string_view, ThenSlots>, 3> k_then_slots{{
    {k_equals, ThenSlots::Value},
    {k_exceeds, ThenSlots::Value},
    {k_stays_between, ThenSlots::Range},
}};

[[nodiscard]] constexpr auto then_slots(std::string_view c) -> std::optional<ThenSlots> {
    for (auto const& [word, slots] : k_then_slots)
        if (c == word)
            return slots;
    return std::nullopt;
}

} // namespace aletheia::detail
