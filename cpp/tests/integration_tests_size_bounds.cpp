// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// The kernel refuses a DBC past a size bound on every command that takes one,
// naming the list that crossed it, and counts what it derives against the
// bound too; through the real library. Each case is a DBC inside every bound
// but the one it crosses, so each builds a list past its bound or a string
// past its cap and hands it through the kernel: the cost is the input's, and
// the mutation binary runs these tests after every other ([costly],
// tools/mutation_cpp_order.py).

#include <catch2/catch_message.hpp>
#include <catch2/catch_test_macros.hpp>

#include <aletheia/aletheia.hpp>

#include <array>
#include <cstdint>
#include <format>
#include <ranges>
#include <stop_token>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "bounds_dbc.hpp"
#include "find_lib.hpp"

using aletheia::test::find_lib;
using aletheia::test::make_bit_message;
using aletheia::test::make_bit_signal;
using aletheia::test::make_bounds_dbc;

using namespace aletheia;

// The values make(0), make(1), ..., make(count - 1).
template<typename Make>
static auto generate(std::uint64_t count, Make make) {
    return std::views::iota(std::uint64_t{0}, count) | std::views::transform(make) |
           std::ranges::to<std::vector>();
}

static auto node_names(std::string_view prefix, std::uint64_t count) -> std::vector<NodeName> {
    return generate(count,
                    [prefix](std::uint64_t i) { return NodeName{std::format("{}{}", prefix, i)}; });
}

static auto with_signal_groups(std::uint64_t count) -> DbcDefinition {
    auto dbc = make_bounds_dbc();
    dbc.signal_groups = generate(count, [](std::uint64_t i) {
        return DbcSignalGroup{.name = std::format("G{}", i), .signals = {}};
    });
    return dbc;
}

static auto with_environment_vars(std::uint64_t count) -> DbcDefinition {
    auto dbc = make_bounds_dbc();
    dbc.environment_vars = generate(count, [](std::uint64_t i) {
        return DbcEnvironmentVar{.name = std::format("E{}", i),
                                 .var_type = DbcVarType::Int,
                                 .initial = Rational{0, 1},
                                 .minimum = Rational{0, 1},
                                 .maximum = Rational{1, 1}};
    });
    return dbc;
}

static auto with_unresolved_value_descs(std::uint64_t count) -> DbcDefinition {
    auto dbc = make_bounds_dbc();
    dbc.unresolved_value_descs = generate(count, [](std::uint64_t /*i*/) {
        return DbcRawValueDesc{
            .can_id = CanId{StandardId::create(999).value()}, .signal_name = "Q", .entries = {}};
    });
    return dbc;
}

static auto with_senders(std::uint64_t count) -> DbcDefinition {
    auto dbc = make_bounds_dbc();
    dbc.messages.front().senders = node_names("N", count);
    return dbc;
}

static auto with_receivers(std::uint64_t count) -> DbcDefinition {
    auto dbc = make_bounds_dbc();
    dbc.messages.front().signals.front().receivers = node_names("N", count);
    return dbc;
}

static auto with_signal_group_members(std::uint64_t count) -> DbcDefinition {
    auto dbc = make_bounds_dbc();
    dbc.signal_groups = {DbcSignalGroup{
        .name = "G",
        .signals =
            generate(count, [](std::uint64_t i) { return SignalName{std::format("S{}", i)}; }),
    }};
    return dbc;
}

static auto with_enum_labels(std::uint64_t count) -> DbcDefinition {
    auto dbc = make_bounds_dbc();
    dbc.attributes = {DbcAttrDef{
        .name = "A",
        .scope = DbcAttrScope::Network,
        .attr_type =
            DbcAttrTypeEnum{
                .values = generate(count, [](std::uint64_t i) { return std::format("v{}", i); })},
    }};
    return dbc;
}

// An eight-bit selector Mx, and S present for each of the first `count` of
// its values.
static auto with_multiplex_values(std::uint64_t count) -> DbcDefinition {
    auto selector = make_bit_signal("Mx");
    selector.bit_length = BitLength{8};
    selector.maximum = RationalBound{Rational{255, 1}};
    auto muxed = make_bit_signal("S");
    muxed.start_bit = BitPosition{8};
    muxed.presence = Multiplexed{
        .multiplexor = SignalName{"Mx"},
        .multiplex_values = generate(
            count, [](std::uint64_t i) { return MultiplexValue{static_cast<std::uint32_t>(i)}; }),
    };
    auto dbc = make_bounds_dbc();
    dbc.messages = {make_bit_message(256, {std::move(selector), std::move(muxed)})};
    return dbc;
}

// A refusal of a DBC past a size bound, as the client surfaces it: the
// bound_info names the part of the DBC that crossed the bound, and the
// message prefixes it with the command that refused.
template<typename T>
static void check_bound_refusal(const Result<T>& result, std::string_view bound_kind,
                                std::string_view field, std::string_view message,
                                std::uint64_t observed, std::uint64_t limit) {
    REQUIRE_FALSE(result.has_value());
    auto const& error = result.error();
    CHECK(error.kind() == ErrorKind::InputBoundExceeded);
    CHECK(error.code() == ErrorCode::InputBoundExceeded);
    CHECK(error.message() == message);
    REQUIRE(error.bound_info().has_value());
    CHECK(error.bound_info()->bound_kind == bound_kind);
    CHECK(error.bound_info()->field == field);
    CHECK(error.bound_info()->observed == observed);
    CHECK(error.bound_info()->limit == limit);
}

TEST_CASE("parse_dbc refuses a DBC past a size bound, naming the list that crossed it",
          "[integration][dbc][input_bounds][costly]") {
    AletheiaClient client(make_ffi_backend(find_lib()));
    struct Case {
        std::string_view context;
        std::uint64_t limit;
        DbcDefinition (*make)(std::uint64_t count);
    };
    for (auto const& [context, limit, make] : std::to_array<Case>({
             {.context = "signal groups array",
              .limit = max_signal_groups_per_file,
              .make = with_signal_groups},
             {.context = "environment variables array",
              .limit = max_environment_variables_per_file,
              .make = with_environment_vars},
             {.context = "unresolved value descriptions array",
              .limit = max_unresolved_value_descriptions_per_file,
              .make = with_unresolved_value_descs},
             {.context = "senders array", .limit = max_nodes_per_file, .make = with_senders},
             {.context = "receivers array", .limit = max_nodes_per_file, .make = with_receivers},
             {.context = "signal group members array",
              .limit = max_signals_per_message,
              .make = with_signal_group_members},
             {.context = "enum labels array",
              .limit = max_enum_labels_per_attribute,
              .make = with_enum_labels},
             {.context = "multiplex values array",
              .limit = max_multiplex_values_per_signal,
              .make = with_multiplex_values},
         })) {
        CAPTURE(context);
        check_bound_refusal(client.parse_dbc(std::stop_token{}, make(limit + 1)),
                            bound_kind_array_cardinality, context,
                            std::format("ParseDBC: {}: array cardinality {} exceeds limit {}",
                                        context, limit + 1, limit),
                            limit + 1, limit);
    }
}

TEST_CASE("validate_dbc refuses a DBC past a size bound",
          "[integration][dbc][input_bounds][costly]") {
    AletheiaClient client(make_ffi_backend(find_lib()));
    check_bound_refusal(
        client.validate_dbc(std::stop_token{},
                            with_environment_vars(max_environment_variables_per_file + 1)),
        bound_kind_array_cardinality, "environment variables array",
        "ValidateDBC: environment variables array: array cardinality 10001 exceeds limit 10000",
        max_environment_variables_per_file + 1, max_environment_variables_per_file);
}

TEST_CASE("format_dbc_text refuses a DBC past a size bound rather than formatting it",
          "[integration][dbc][format][input_bounds][costly]") {
    AletheiaClient client(make_ffi_backend(find_lib()));

    check_bound_refusal(
        client.format_dbc_text(std::stop_token{},
                               with_signal_groups(max_signal_groups_per_file + 1)),
        bound_kind_array_cardinality, "signal groups array",
        "FormatDBCText: signal groups array: array cardinality 10001 exceeds limit 10000",
        max_signal_groups_per_file + 1, max_signal_groups_per_file);

    auto long_version = make_bounds_dbc();
    long_version.version = std::string(max_string_length_characters + 1, 'x');
    check_bound_refusal(client.format_dbc_text(std::stop_token{}, long_version),
                        bound_kind_string_length, "version string",
                        "FormatDBCText: version string: string length 65537 exceeds limit 65536",
                        max_string_length_characters + 1, max_string_length_characters);
}

TEST_CASE("format_dbc_text counts the nodes it derives from the senders against the node bound",
          "[integration][dbc][format][input_bounds][costly]") {
    AletheiaClient client(make_ffi_backend(find_lib()));
    // Two messages sent by ECU, each with its own senders list inside the
    // node bound; with no nodes declared, the formatter derives ECU and both
    // lists, and the derived count is past the bound.
    constexpr auto per_message = (max_nodes_per_file / 2) + 1;
    auto dbc = make_bounds_dbc();
    dbc.messages.front().senders = node_names("A", per_message);
    dbc.messages.push_back(make_bit_message(257, {make_bit_signal("S")}));
    dbc.messages.back().senders = node_names("B", per_message);

    // Each list is inside its own bound, so the load route takes the DBC.
    REQUIRE(client.parse_dbc(std::stop_token{}, dbc).has_value());
    check_bound_refusal(client.format_dbc_text(std::stop_token{}, dbc),
                        bound_kind_array_cardinality, "nodes array",
                        "FormatDBCText: nodes array: array cardinality 10003 exceeds limit 10000",
                        1 + (2 * per_message), max_nodes_per_file);
}
