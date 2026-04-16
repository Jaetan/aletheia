// SPDX-License-Identifier: BSD-2-Clause
//
// YAML check loader implementation.
//
#include <aletheia/yaml.hpp>

#include "detail/loader_utils.hpp"

#include <yaml-cpp/yaml.h>

#include <chrono>
#include <cstdint>
#include <expected>
#include <filesystem>
#include <stdexcept>
#include <string>
#include <string_view>
#include <vector>

namespace aletheia {

namespace {

// ---------------------------------------------------------------------------
// YAML field extractors with error context
// ---------------------------------------------------------------------------

auto get_str(const YAML::Node& node, const std::string& key, const std::string& ctx)
    -> std::string {
    auto child = node[key];
    if (!child || !child.IsScalar())
        throw std::runtime_error(ctx + ": missing or invalid '" + key + "' (expected string)");
    return child.as<std::string>();
}

auto get_number(const YAML::Node& node, const std::string& key, const std::string& ctx) -> double {
    auto child = node[key];
    if (!child || !child.IsScalar())
        throw std::runtime_error(ctx + ": missing or invalid '" + key + "' (expected number)");
    // Reject booleans: yaml-cpp parses "true"/"false" as scalars too
    auto raw = child.as<std::string>();
    if (raw == "true" || raw == "false" || raw == "TRUE" || raw == "FALSE" || raw == "True" ||
        raw == "False")
        throw std::runtime_error(ctx + ": missing or invalid '" + key + "' (expected number)");
    try {
        return child.as<double>();
    } catch (const YAML::BadConversion&) {
        throw std::runtime_error(ctx + ": missing or invalid '" + key + "' (expected number)");
    }
}

auto get_int(const YAML::Node& node, const std::string& key, const std::string& ctx)
    -> std::int64_t {
    auto child = node[key];
    if (!child || !child.IsScalar())
        throw std::runtime_error(ctx + ": missing or invalid '" + key + "' (expected integer)");
    try {
        return child.as<std::int64_t>();
    } catch (const YAML::BadConversion&) {
        throw std::runtime_error(ctx + ": missing or invalid '" + key + "' (expected integer)");
    }
}

auto get_map(const YAML::Node& node, const std::string& key, const std::string& ctx) -> YAML::Node {
    auto child = node[key];
    if (!child || !child.IsMap())
        throw std::runtime_error(ctx + ": missing or invalid '" + key + "' (expected mapping)");
    return child;
}

// ---------------------------------------------------------------------------
// Check name extraction
// ---------------------------------------------------------------------------

auto check_name(const YAML::Node& entry) -> std::string {
    auto name_node = entry["name"];
    if (name_node && name_node.IsScalar())
        return name_node.as<std::string>();
    return "<unnamed>";
}

auto ctx(const std::string& name) -> std::string {
    return "Check '" + name + "'";
}

// ---------------------------------------------------------------------------
// Simple check parser
// ---------------------------------------------------------------------------

auto parse_simple_check(const YAML::Node& entry, const std::string& name) -> CheckResult {
    auto condition = get_str(entry, "condition", ctx(name));
    auto signal = get_str(entry, "signal", ctx(name));

    if (!detail::is_simple_condition(condition))
        throw std::runtime_error(ctx(name) + ": unknown condition '" + condition + "'");

    if (detail::is_simple_value_condition(condition)) {
        if (!entry["value"])
            throw std::runtime_error(ctx(name) + ": condition '" + condition +
                                     "' requires 'value'");
        auto value = PhysicalValue{Rational::from_double(get_number(entry, "value", ctx(name)))};
        return detail::dispatch_simple(signal, condition, value);
    }

    if (detail::is_simple_range_condition(condition)) {
        if (!entry["min"] || !entry["max"])
            throw std::runtime_error(ctx(name) + ": condition '" + condition +
                                     "' requires 'min' and 'max'");
        auto lo = PhysicalValue{Rational::from_double(get_number(entry, "min", ctx(name)))};
        auto hi = PhysicalValue{Rational::from_double(get_number(entry, "max", ctx(name)))};
        return Check::signal(signal).stays_between(lo, hi);
    }

    if (detail::is_simple_settles_condition(condition)) {
        if (!entry["min"] || !entry["max"])
            throw std::runtime_error(ctx(name) +
                                     ": condition 'settles_between' requires 'min' and 'max'");
        if (!entry["within_ms"])
            throw std::runtime_error(ctx(name) +
                                     ": condition 'settles_between' requires 'within_ms'");
        auto lo = PhysicalValue{Rational::from_double(get_number(entry, "min", ctx(name)))};
        auto hi = PhysicalValue{Rational::from_double(get_number(entry, "max", ctx(name)))};
        auto ms = std::chrono::milliseconds{get_int(entry, "within_ms", ctx(name))};
        return Check::signal(signal).settles_between(lo, hi).within(ms);
    }

    // equals
    if (!entry["value"])
        throw std::runtime_error(ctx(name) + ": condition 'equals' requires 'value'");
    auto value = PhysicalValue{Rational::from_double(get_number(entry, "value", ctx(name)))};
    return Check::signal(signal).equals(value).always();
}

// ---------------------------------------------------------------------------
// When/Then check parser
// ---------------------------------------------------------------------------

auto parse_when_then_check(const YAML::Node& entry, const std::string& name) -> CheckResult {
    if (!entry["then"])
        throw std::runtime_error(ctx(name) + ": must have 'signal' or 'when'/'then'");
    if (!entry["within_ms"])
        throw std::runtime_error(ctx(name) + ": when/then checks require 'within_ms'");

    auto when = get_map(entry, "when", ctx(name));
    auto then = get_map(entry, "then", ctx(name));
    auto within_ms = std::chrono::milliseconds{get_int(entry, "within_ms", ctx(name))};

    // When clause
    auto when_cond = get_str(when, "condition", ctx(name));
    if (!detail::is_when_condition(when_cond))
        throw std::runtime_error(ctx(name) + ": unknown when condition '" + when_cond + "'");

    auto when_signal = get_str(when, "signal", ctx(name));
    auto when_value = PhysicalValue{Rational::from_double(get_number(when, "value", ctx(name)))};
    auto when_builder = Check::when(when_signal);
    auto when_result = detail::dispatch_when(when_builder, when_cond, when_value);

    // Then clause
    auto then_cond = get_str(then, "condition", ctx(name));
    if (!detail::is_then_condition(then_cond))
        throw std::runtime_error(ctx(name) + ": unknown then condition '" + then_cond + "'");

    auto then_signal = get_str(then, "signal", ctx(name));
    auto then_builder = when_result.then(then_signal);

    if (then_cond == "equals") {
        auto val = PhysicalValue{Rational::from_double(get_number(then, "value", ctx(name)))};
        return then_builder.equals(val).within(within_ms);
    }
    if (then_cond == "exceeds") {
        auto val = PhysicalValue{Rational::from_double(get_number(then, "value", ctx(name)))};
        return then_builder.exceeds(val).within(within_ms);
    }
    // stays_between
    if (!then["min"] || !then["max"])
        throw std::runtime_error(ctx(name) +
                                 ": then condition 'stays_between' requires 'min' and 'max'");
    auto lo = PhysicalValue{Rational::from_double(get_number(then, "min", ctx(name)))};
    auto hi = PhysicalValue{Rational::from_double(get_number(then, "max", ctx(name)))};
    return then_builder.stays_between(lo, hi).within(within_ms);
}

// ---------------------------------------------------------------------------
// Single check entry parser
// ---------------------------------------------------------------------------

auto parse_check(const YAML::Node& entry) -> CheckResult {
    auto name = check_name(entry);

    CheckResult result = [&] {
        if (entry["when"])
            return parse_when_then_check(entry, name);
        if (entry["signal"])
            return parse_simple_check(entry, name);
        throw std::runtime_error(ctx(name) + ": must have 'signal' or 'when'/'then'");
    }();

    // Apply metadata
    auto name_node = entry["name"];
    if (name_node && name_node.IsScalar())
        result.named(name_node.as<std::string>());
    auto sev_node = entry["severity"];
    if (sev_node && sev_node.IsScalar())
        result.severity(sev_node.as<std::string>());

    return result;
}

// ---------------------------------------------------------------------------
// Top-level YAML parser
// ---------------------------------------------------------------------------

auto parse_yaml_checks(const YAML::Node& root) -> Result<std::vector<CheckResult>> {
    if (!root || !root.IsMap() || !root["checks"])
        return std::unexpected(
            AletheiaError{ErrorKind::Validation, "YAML must contain a 'checks' list"});

    auto checks_node = root["checks"];
    if (!checks_node.IsSequence())
        return std::unexpected(
            AletheiaError{ErrorKind::Validation, "YAML must contain a 'checks' list"});

    std::vector<CheckResult> results;
    for (const auto& entry : checks_node) {
        if (!entry.IsMap())
            return std::unexpected(
                AletheiaError{ErrorKind::Validation, "Each check must be a YAML mapping"});
        try {
            results.push_back(parse_check(entry));
        } catch (const std::runtime_error& ex) {
            return std::unexpected(AletheiaError{ErrorKind::Validation, ex.what()});
        }
    }
    return results;
}

} // namespace

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

auto load_checks_from_yaml(const std::filesystem::path& path) -> Result<std::vector<CheckResult>> {
    if (!std::filesystem::exists(path))
        return std::unexpected(
            AletheiaError{ErrorKind::Validation, "YAML file not found: " + path.string()});

    try {
        auto root = YAML::LoadFile(path.string());
        return parse_yaml_checks(root);
    } catch (const YAML::Exception& ex) {
        return std::unexpected(AletheiaError{ErrorKind::Validation, std::string(ex.what())});
    }
}

auto load_checks_from_yaml_string(std::string_view yaml) -> Result<std::vector<CheckResult>> {
    try {
        auto root = YAML::Load(std::string(yaml));
        return parse_yaml_checks(root);
    } catch (const YAML::Exception& ex) {
        return std::unexpected(AletheiaError{ErrorKind::Validation, std::string(ex.what())});
    }
}

} // namespace aletheia
