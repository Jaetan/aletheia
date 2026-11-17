// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// The kernel's reading of a property as a builder makes it, and of a time
// bound as a loader reads one. A builder hands what it made to
// `aletheia_check_property`, which reads it as set_properties reads a property
// and refuses it with set_properties' reason, so a check is refused where it
// is built. Both entries are consumers of the GHC runtime, as the renderer and
// the decimal parser are: they never start it, since a start fixes the core
// count for the process, and refuse while it is down.
#include <aletheia/detail/checked.hpp>
#include <aletheia/error.hpp>
#include <aletheia/ltl.hpp>
#include <aletheia/types.hpp>

#include "detail/ffi_abi.hpp"
#include "detail/json.hpp"
#include "detail/rts_init.hpp"

#include <expected>
#include <memory>
#include <string>
#include <string_view>
#include <utility>
#include <variant>

namespace aletheia {

// The error envelope an entry outside a session wrote on a refusal, freed
// once read and typed as the caller's own mistake, as `Rational::from_decimal`
// types a refusal; a refusal without one is a Protocol error naming `symbol`.
static auto entry_refusal(detail::RuntimeEntries const& entries, std::string_view symbol,
                          char* envelope) -> AletheiaError {
    if (envelope == nullptr)
        return AletheiaError{ErrorKind::Protocol,
                             std::string{symbol} + " refused without an error"};
    auto const deleter = [&entries](char* p) { entries.free_str(p); };
    std::unique_ptr<char, decltype(deleter)> const guard{envelope, deleter};
    return detail::binary_refusal(detail::c_string_view(envelope), ErrorKind::Validation);
}

// Every field, ordering, denominator and time bound is decided, and each
// signal name as an identifier; whether a DBC carries the signal is left to
// set_properties. The refusal's text is the reason set_properties gives after
// "SetProperties: property N: ".
auto detail::checked_formula(LtlFormula f) -> Result<LtlFormula> {
    auto const property = serialize_property(f);
    if (!property)
        return std::unexpected(error_of(property));
    auto const started = started_entries("building a check");
    if (!started)
        return std::unexpected(error_of(started));
    auto const& entries = started.value();
    auto const text = ffi_text(property.value());
    FfiPropertyCheck out{.err = nullptr};
    if (entries.check_property(&text, &out) != 0)
        return std::unexpected(entry_refusal(entries, "aletheia_check_property", out.err));
    return f;
}

auto detail::checked_predicate(Predicate p) -> Result<Predicate> {
    return checked_formula(Atomic{.predicate = std::move(p)}).transform([](LtlFormula f) {
        return std::get<Atomic>(std::move(f.value)).predicate;
    });
}

auto TimeBound::parse(std::string_view text) -> Result<TimeBound> {
    auto const started = detail::started_entries("reading a time bound");
    if (!started)
        return std::unexpected(detail::error_of(started));
    auto const& entries = started.value();
    auto const input = detail::ffi_text(text);
    detail::FfiTimeBound out{.microseconds = 0, .err = nullptr};
    if (entries.parse_time_bound(&input, &out) != 0)
        return std::unexpected(entry_refusal(entries, "aletheia_parse_time_bound", out.err));
    return TimeBound{out.microseconds};
}

} // namespace aletheia
