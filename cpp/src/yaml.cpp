// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// YAML check loader implementation.
//
#include <aletheia/detail/checked.hpp>
#include <aletheia/yaml.hpp>

#include "detail/loader_utils.hpp"

#include <yaml-cpp/yaml.h>

#include <chrono>
#include <expected>
#include <filesystem>
#include <stdexcept>
#include <string>
#include <string_view>
#include <vector>

namespace aletheia {

// ---------------------------------------------------------------------------
// YAML field extractors with error context
// ---------------------------------------------------------------------------

// The refusal every field reader below throws, for a key that is absent or
// that names a node of another kind; the wording is shared with the Python
// loader, so it has one owner here.
static auto missing_or_invalid(std::string const& ctx, std::string const& key,
                               std::string_view expected) -> std::runtime_error {
    return std::runtime_error(ctx + ": missing or invalid '" + key + "' (expected " +
                              std::string{expected} + ")");
}

// The child a key names, refused in the loader's words when absent. Every
// reader takes its child through here, so an undefined node never reaches a
// kind test, whose refusal would be yaml-cpp's rather than the loader's.
static auto require_child(YAML::Node const& node, std::string const& key, std::string const& ctx,
                          std::string_view expected) -> YAML::Node {
    auto const child = node[key];
    if (!child)
        throw missing_or_invalid(ctx, key, expected);
    return child;
}

static auto get_str(YAML::Node const& node, std::string const& key, std::string const& ctx)
    -> std::string {
    auto const child = require_child(node, key, ctx, "string");
    if (!child.IsScalar())
        throw missing_or_invalid(ctx, key, "string");
    return child.as<std::string>();
}

// Read a numeric scalar as an exact Rational through `detail::read_decimal`,
// located at the check and the key. yaml-cpp hands every scalar as its text,
// tag and quotes aside, so the kernel reads the number as the document spells
// it: `11.5`, `!!float 11.5` and `"11.5"` are each 23/2, and `0x1F` or `1e3` is
// the kernel's refusal rather than a value a YAML resolver chose. The runtime
// must be up (`start_runtime` or a backend). An absent key and a node that is
// not a scalar are the loader's own refusal, naming `expected` as what it reads.
static auto get_decimal(YAML::Node const& node, std::string const& key, std::string const& ctx,
                        std::string_view expected = "number") -> Rational {
    auto const child = require_child(node, key, ctx, expected);
    if (!child.IsScalar())
        throw missing_or_invalid(ctx, key, expected);
    return detail::read_decimal(child.as<std::string>(), ctx, key);
}

// Read `within_ms`, a check's bound in milliseconds, as get_decimal reads a
// number, so the kernel decides what the text is. The loader refuses at the
// check a reading that is not whole, one that is negative, and one whose
// microseconds the check builder's conversion refuses as overflowing int64.
static auto get_within_ms(YAML::Node const& node, std::string const& ctx)
    -> std::chrono::milliseconds {
    auto const value = get_decimal(node, "within_ms", ctx, "integer");
    if (value.denominator() != 1)
        throw std::runtime_error(ctx + ": 'within_ms' must be a whole number, got " +
                                 node["within_ms"].as<std::string>());
    if (value.numerator() < 0)
        throw std::runtime_error(ctx + ": 'within_ms' must be non-negative, got " +
                                 node["within_ms"].as<std::string>());
    auto const ms = std::chrono::milliseconds{value.numerator()};
    if (auto const us = detail::checked_ms_to_us(ms); !us)
        throw std::runtime_error(
            ctx + ": invalid 'within_ms': " + std::string{detail::error_of(us).message()});
    return ms;
}

static auto get_map(YAML::Node const& node, std::string const& key, std::string const& ctx)
    -> YAML::Node {
    auto const child = require_child(node, key, ctx, "mapping");
    if (!child.IsMap())
        throw missing_or_invalid(ctx, key, "mapping");
    return child;
}

// ---------------------------------------------------------------------------
// Check name extraction
// ---------------------------------------------------------------------------

static auto check_name(YAML::Node const& entry) -> std::string {
    auto const name_node = entry["name"];
    if (name_node && name_node.IsScalar())
        return name_node.as<std::string>();
    return "<unnamed>";
}

static auto ctx(std::string const& name) -> std::string {
    return "Check '" + name + "'";
}

// ---------------------------------------------------------------------------
// Simple check parser
// ---------------------------------------------------------------------------

static auto parse_simple_check(YAML::Node const& entry, std::string const& name) -> CheckResult {
    auto const condition = get_str(entry, "condition", ctx(name));
    auto const signal = get_str(entry, "signal", ctx(name));

    if (!detail::is_simple_condition(condition))
        throw std::runtime_error(ctx(name) + ": unknown condition '" + condition + "'");

    if (detail::is_simple_value_condition(condition)) {
        if (!entry["value"])
            throw std::runtime_error(ctx(name) + ": condition '" + condition +
                                     "' requires 'value'");
        auto const value = PhysicalValue{get_decimal(entry, "value", ctx(name))};
        return detail::dispatch_simple(signal, condition, value);
    }

    if (detail::is_simple_range_condition(condition)) {
        if (!entry["min"] || !entry["max"])
            throw std::runtime_error(ctx(name) + ": condition '" + condition +
                                     "' requires 'min' and 'max'");
        auto const lo = PhysicalValue{get_decimal(entry, "min", ctx(name))};
        auto const hi = PhysicalValue{get_decimal(entry, "max", ctx(name))};
        return detail::built_check(check::signal(signal).stays_between(lo, hi));
    }

    if (detail::is_simple_settles_condition(condition)) {
        if (!entry["min"] || !entry["max"])
            throw std::runtime_error(ctx(name) +
                                     ": condition 'settles_between' requires 'min' and 'max'");
        if (!entry["within_ms"])
            throw std::runtime_error(ctx(name) +
                                     ": condition 'settles_between' requires 'within_ms'");
        auto const lo = PhysicalValue{get_decimal(entry, "min", ctx(name))};
        auto const hi = PhysicalValue{get_decimal(entry, "max", ctx(name))};
        auto const ms = get_within_ms(entry, ctx(name));
        return detail::built_check(check::signal(signal).settles_between(lo, hi).within(ms));
    }

    // equals
    if (!entry["value"])
        throw std::runtime_error(ctx(name) + ": condition 'equals' requires 'value'");
    auto const value = PhysicalValue{get_decimal(entry, "value", ctx(name))};
    return check::signal(signal).equals(value).always();
}

// ---------------------------------------------------------------------------
// When/Then check parser
// ---------------------------------------------------------------------------

static auto parse_when_then_check(YAML::Node const& entry, std::string const& name) -> CheckResult {
    if (!entry["then"])
        throw std::runtime_error(ctx(name) + ": must have 'signal' or 'when'/'then'");
    if (!entry["within_ms"])
        throw std::runtime_error(ctx(name) + ": when/then checks require 'within_ms'");

    auto const when = get_map(entry, "when", ctx(name));
    auto const then = get_map(entry, "then", ctx(name));
    auto const within_ms = get_within_ms(entry, ctx(name));

    // When clause
    auto const when_cond = get_str(when, "condition", ctx(name));
    if (!detail::is_when_condition(when_cond))
        throw std::runtime_error(ctx(name) + ": unknown when condition '" + when_cond + "'");

    auto const when_signal = get_str(when, "signal", ctx(name));
    auto const when_value = PhysicalValue{get_decimal(when, "value", ctx(name))};
    auto const when_builder = check::when(when_signal);
    auto const when_result = detail::dispatch_when(when_builder, when_cond, when_value);

    // Then clause
    auto const then_cond = get_str(then, "condition", ctx(name));
    // The word is held to the vocabulary by taking its slots: one lookup
    // answers both whether the obligation is known and what it reads.
    auto const slots = detail::then_slots(then_cond);
    if (!slots)
        throw std::runtime_error(ctx(name) + ": unknown then condition '" + then_cond + "'");

    auto const then_signal = get_str(then, "signal", ctx(name));
    auto const then_builder = when_result.then(then_signal);

    // Which keys the obligation reads is the vocabulary's business, not this
    // loader's; which keys they are, and what to say when one is missing, is
    // this loader's. Only the slots the obligation reads are handed over.
    detail::ThenSlotValues read;
    switch (slots.value()) {
    case detail::ThenSlots::Value:
        read.emplace("value", PhysicalValue{get_decimal(then, "value", ctx(name))});
        break;
    case detail::ThenSlots::Range:
        if (!then["min"] || !then["max"])
            throw std::runtime_error(ctx(name) + ": then condition '" + then_cond +
                                     "' requires 'min' and 'max'");
        read.emplace("lo", PhysicalValue{get_decimal(then, "min", ctx(name))});
        read.emplace("hi", PhysicalValue{get_decimal(then, "max", ctx(name))});
        break;
    }
    return detail::dispatch_then(then_builder, then_cond, read, within_ms);
}

// ---------------------------------------------------------------------------
// Single check entry parser
// ---------------------------------------------------------------------------

static auto parse_check(YAML::Node const& entry) -> CheckResult {
    auto const name = check_name(entry);

    auto result = [&] {
        if (entry["when"])
            return parse_when_then_check(entry, name);
        if (entry["signal"])
            return parse_simple_check(entry, name);
        throw std::runtime_error(ctx(name) + ": must have 'signal' or 'when'/'then'");
    }();

    // Apply metadata
    auto const name_node = entry["name"];
    if (name_node && name_node.IsScalar())
        result.named(name_node.as<std::string>());
    auto const sev_node = entry["severity"];
    if (sev_node && sev_node.IsScalar())
        result.severity(sev_node.as<std::string>());

    return result;
}

// ---------------------------------------------------------------------------
// Top-level YAML parser
// ---------------------------------------------------------------------------

static auto parse_yaml_checks(YAML::Node const& root) -> Result<std::vector<CheckResult>> {
    if (!root.IsMap() || !root["checks"])
        return std::unexpected(
            AletheiaError{ErrorKind::Validation, "YAML must contain a 'checks' list"});

    auto const checks_node = root["checks"];
    if (!checks_node.IsSequence())
        return std::unexpected(
            AletheiaError{ErrorKind::Validation, "YAML must contain a 'checks' list"});

    std::vector<CheckResult> results;
    for (auto const& entry : checks_node) {
        if (!entry.IsMap())
            return std::unexpected(
                AletheiaError{ErrorKind::Validation, "Each check must be a YAML mapping"});
        try {
            results.push_back(parse_check(entry));
        } catch (detail::AletheiaException const& ex) {
            // A refused number, located, or a runtime failure keeps the error
            // as thrown; any other defect of the document is a Validation one.
            return std::unexpected(ex.error());
        } catch (std::runtime_error const& ex) {
            return std::unexpected(AletheiaError{ErrorKind::Validation, ex.what()});
        }
    }
    return results;
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

auto load_checks_from_yaml(std::filesystem::path const& path) -> Result<std::vector<CheckResult>> {
    // Reject symlinks and cap the raw size before handing the path to yaml-cpp.
    // YAML has no compressed container, so the uncompressed-size walk the .xlsx
    // loader does over its ZIP entries has no counterpart here.
    if (auto const v = detail::validate_loader_path(path, "YAML"); !v)
        return std::unexpected(detail::error_of(v));
    if (auto const v = detail::check_file_size_bound(path); !v)
        return std::unexpected(detail::error_of(v));

    try {
        auto const root = YAML::LoadFile(path.string());
        return parse_yaml_checks(root);
    } catch (YAML::Exception const& ex) {
        return std::unexpected(AletheiaError{ErrorKind::Validation, std::string(ex.what())});
    }
}

auto load_checks_from_yaml_string(std::string_view yaml) -> Result<std::vector<CheckResult>> {
    // Bound the in-memory input before the YAML::Load copy/parse, mirroring the
    // file loader's check_file_size_bound (and Go/Rust, which bound their inline
    // YAML loaders).  AGENTS.md trust boundary: every check loader, file or
    // inline, caps input at max_dbc_text_bytes.
    if (auto const v = detail::check_input_size_bound(yaml.size()); !v)
        return std::unexpected(detail::error_of(v));
    try {
        auto const root = YAML::Load(std::string(yaml));
        return parse_yaml_checks(root);
    } catch (YAML::Exception const& ex) {
        return std::unexpected(AletheiaError{ErrorKind::Validation, std::string(ex.what())});
    }
}

} // namespace aletheia
