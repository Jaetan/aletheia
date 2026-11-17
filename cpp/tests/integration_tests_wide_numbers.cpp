// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The numbers the kernel carries past 64 bits, through the real library. Each
// number kind has its own bound, decided by the kernel when it reads the
// number: a rational's numerator magnitude and denominator at most 2^128-1, a
// multiplex value at most 2^128-1, a value-description key signed with its
// magnitude at most 2^128-1, and a time bound at most 2^64-1 microseconds. A
// refusal past a bound whose measured value passes the reported ceiling names
// no number.

#include <catch2/catch_message.hpp>
#include <catch2/catch_test_macros.hpp>

#include <aletheia/aletheia.hpp>
#include <aletheia/detail/rational_renderer.hpp>

#include <array>
#include <cstddef>
#include <cstdint>
#include <format>
#include <limits>
#include <ranges>
#include <stop_token>
#include <string>
#include <string_view>
#include <utility>
#include <variant>
#include <vector>

#include "detail/json.hpp"
#include "find_lib.hpp"
#include "kernel_session.hpp"
#include "required.hpp"
#include "u128_testing.hpp"

using aletheia::test::find_lib;
using aletheia::test::KernelSession;
using aletheia::test::required;

using namespace aletheia;

constexpr auto u64_max = std::numeric_limits<std::uint64_t>::max();
constexpr auto u128_max = max_rational_component_magnitude;

// 2^128-1 and 2^128 as a DBC text writes them.
constexpr std::string_view u128_max_digits = "340282366920938463463374607431768211455";
constexpr std::string_view two_to_128_digits = "340282366920938463463374607431768211456";

// The factor opendbc's vw_mlb.dbc gives OBD_Abs_Load_Val, 100/255 printed to
// 17 places, so a value's reduced numerator passes 64 bits on most raw values.
constexpr unsigned __int128 vw_mlb_numerator = 39'215'686'274'509'803;
constexpr unsigned __int128 vw_mlb_denominator = 100'000'000'000'000'000;

static auto message_id() -> CanId {
    return CanId{StandardId::create(0x100).value()};
}
static auto eight_bytes() -> Dlc {
    return Dlc::create(8).value();
}

// `numerator / denominator`, reduced.
static auto ratio(unsigned __int128 numerator, unsigned __int128 denominator) -> Rational {
    return Rational::make(false, numerator, denominator).value();
}

// A little-endian unsigned signal at bit zero, offset zero, its range from
// zero.
static auto unsigned_signal(std::string name, std::uint16_t length, Rational factor,
                            Rational maximum) -> DbcSignal {
    return DbcSignal{
        .name = SignalName{std::move(name)},
        .start_bit = BitPosition{0},
        .bit_length = BitLength{length},
        .byte_order = ByteOrder::LittleEndian,
        .is_signed = false,
        .factor = RationalFactor{factor},
        .offset = RationalOffset{Rational{0, 1}},
        .minimum = RationalBound{Rational{0, 1}},
        .maximum = RationalBound{maximum},
        .unit = Unit{""},
        .presence = AlwaysPresent{},
    };
}

// The DBC whose one 8-byte message, 0x100, carries the signal.
static auto one_signal_dbc(DbcSignal signal) -> DbcDefinition {
    return DbcDefinition{
        .version = "1.0",
        .messages = {DbcMessage{
            .id = message_id(),
            .name = MessageName{"Msg"},
            .dlc = eight_bytes(),
            .sender = NodeName{"ECU"},
            .signals = {std::move(signal)},
        }},
    };
}

// A client over the real library.
static auto ffi_client() -> AletheiaClient {
    return required(AletheiaClient::create(required(make_ffi_backend(find_lib()))));
}

namespace {

// One extraction route's reading of a frame.
struct RouteResult {
    std::string_view route;
    ExtractionResult result;
};

// A DBC loaded twice: by a client, whose extract_signals takes the binary
// route once a DBC is loaded, and in a session of its own, whose backend's
// JSON extraction the JSON reply reader reads.
class BothRoutes {
public:
    explicit BothRoutes(DbcDefinition const& dbc) : client_(ffi_client()) {
        REQUIRE(client_.parse_dbc(std::stop_token{}, dbc).has_value());
        auto const command = required(detail::serialize_parse_dbc(dbc));
        REQUIRE(detail::parse_parsed_dbc(session_.process(command)).has_value());
    }

    // The frame of message 0x100 read on each route.
    auto read(FramePayload const& payload) -> std::array<RouteResult, 2> {
        auto binary = required(
            client_.extract_signals(std::stop_token{}, message_id(), eight_bytes(), payload));
        auto const reply = required(session_.backend().extract_signals_binary(
            session_.state(), message_id(), eight_bytes(), payload));
        auto json = required(detail::parse_extraction(reply));
        return {RouteResult{.route = "binary", .result = std::move(binary)},
                RouteResult{.route = "JSON", .result = std::move(json)}};
    }

private:
    AletheiaClient client_;
    KernelSession session_;
};

} // namespace

// Holds that a route read the one value `name` = `want` and no error.
static auto check_one_value(RouteResult const& read, std::string_view name, Rational const& want)
    -> void {
    INFO(read.route << " route");
    CHECK(read.result.errors.empty());
    REQUIRE(read.result.values.size() == 1);
    CHECK(read.result.values.at(0).name == SignalName{std::string{name}});
    CHECK(read.result.values.at(0).value.get() == want);
}

// A one-message, 64-byte DBC text carrying the given SG_ and VAL_ lines,
// after a value table section holding `tables`.
static auto wide_dbc_text(std::string_view tables, std::string_view body) -> std::string {
    return std::format("VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\n{}BO_ 256 M: 64 ECU\n{}",
                       tables, body);
}

// The decimal digits of 5^n.
static auto digits_of_five_to(std::size_t n) -> std::string {
    std::string digits = "1";
    for ([[maybe_unused]] auto const power : std::views::iota(std::size_t{0}, n)) {
        auto carry = 0;
        for (auto& digit : digits | std::views::reverse) {
            auto const product = ((digit - '0') * 5) + carry;
            digit = static_cast<char>('0' + (product % 10));
            carry = product / 10;
        }
        if (carry > 0)
            digits.insert(digits.begin(), static_cast<char>('0' + carry));
    }
    return digits;
}

// Holds that a value description reads the key with the given sign and
// magnitude and the text.
static auto check_entry(DbcValueEntry const& entry, bool negative, std::string_view description)
    -> void {
    CHECK(entry.value == SignMagnitude{.negative = negative, .magnitude = u128_max});
    CHECK(entry.description == description);
}

// Holds the extremes DBC's numbers as a reply reads them back: the multiplex
// value 2^128-1, and the keys -(2^128-1) and 2^128-1 of the signal's value
// descriptions and of the value table.
static auto check_extremes(DbcDefinition const& dbc) -> void {
    REQUIRE(dbc.messages.size() == 1);
    auto const& signals = dbc.messages.at(0).signals;
    REQUIRE(signals.size() == 3);
    auto const* const selected = std::get_if<Multiplexed>(&signals.at(1).presence);
    REQUIRE(selected != nullptr);
    CHECK(selected->multiplexor == SignalName{"Mx"});
    CHECK(selected->multiplex_values == std::vector{MultiplexValue{u128_max}});
    auto const& descriptions = signals.at(2).value_descriptions;
    REQUIRE(descriptions.size() == 2);
    check_entry(descriptions.at(0), true, "Lowest");
    check_entry(descriptions.at(1), false, "Highest");
    REQUIRE(dbc.value_tables.size() == 1);
    CHECK(dbc.value_tables.at(0).name == "Extremes");
    auto const& entries = dbc.value_tables.at(0).entries;
    REQUIRE(entries.size() == 2);
    check_entry(entries.at(0), true, "Below");
    check_entry(entries.at(1), false, "Above");
}

TEST_CASE("a 64-bit raw value extracts exactly on both routes", "[integration][wide]") {
    BothRoutes routes{
        one_signal_dbc(unsigned_signal("Big", 64, Rational{1, 1}, Rational::integer(u64_max)))};
    for (auto const& read : routes.read(FramePayload(8, std::byte{0xFF})))
        check_one_value(read, "Big", Rational::integer(u64_max));
}

TEST_CASE("a frame built from a 64-bit value sets every bit", "[integration][wide]") {
    auto client = ffi_client();
    auto const dbc =
        one_signal_dbc(unsigned_signal("Big", 64, Rational{1, 1}, Rational::integer(u64_max)));
    REQUIRE(client.parse_dbc(std::stop_token{}, dbc).has_value());
    auto const values = std::to_array<SignalValue>(
        {{.name = SignalName{"Big"}, .value = PhysicalValue{Rational::integer(u64_max)}}});
    auto const frame = client.build_frame(std::stop_token{}, message_id(), eight_bytes(), values);
    REQUIRE(frame.has_value());
    CHECK(*frame == FramePayload(8, std::byte{0xFF}));
}

// A rational crosses into the kernel as two 64-bit words per magnitude, so a
// numerator and a denominator past 2^64-1 reach the kernel's renderer whole.
// Two odd numbers two apart share no factor, so it prints both parts.
TEST_CASE("a rational whose magnitudes pass 2^64-1 reaches the kernel whole",
          "[integration][wide]") {
    auto const backend = required(make_ffi_backend(find_lib())); // brings the runtime up
    constexpr auto two_to_64 = static_cast<unsigned __int128>(u64_max) + 1;
    CHECK(detail::format_rational_ffi(Rational::integer(two_to_64)) == "18446744073709551616");
    CHECK(detail::format_rational_ffi(ratio(two_to_64 + 1, two_to_64 + 3)) ==
          "18446744073709551617/18446744073709551619");
}

TEST_CASE("a 17-place factor extracts its raw values exactly on both routes",
          "[integration][wide]") {
    // The reduced numerators at 471, 4097, 65534 and 65535 pass 64 bits.
    BothRoutes routes{
        one_signal_dbc(unsigned_signal("Load", 16, ratio(vw_mlb_numerator, vw_mlb_denominator),
                                       ratio(vw_mlb_numerator * 0xFFFF, vw_mlb_denominator)))};
    for (auto const raw :
         std::to_array<std::uint16_t>({0, 1, 255, 470, 471, 4097, 0xFFFE, 0xFFFF})) {
        CAPTURE(raw);
        FramePayload payload(8, std::byte{0});
        payload.at(0) = static_cast<std::byte>(raw & 0xFFU);
        payload.at(1) = static_cast<std::byte>(raw >> 8U);
        for (auto const& read : routes.read(payload))
            check_one_value(read, "Load", ratio(vw_mlb_numerator * raw, vw_mlb_denominator));
    }
}

TEST_CASE("a number past the bound is refused with its observed size and limit at 128 bits",
          "[integration][wide]") {
    // 2^128 as a signal maximum: the saturated refusal reports both at
    // 2^128-1 and its message names only the limit.
    auto client = ffi_client();
    auto const text = wide_dbc_text(
        "", std::format(" SG_ S : 0|8@1+ (1,0) [0|{}] \"\" ECU\n", two_to_128_digits));
    auto const refused = client.parse_dbc_text(std::stop_token{}, text);
    REQUIRE_FALSE(refused.has_value());
    CHECK(refused.error().kind() == ErrorKind::InputBoundExceeded);
    CHECK(refused.error().message() ==
          std::format("ParseDBCText: signal maximum: rational component magnitude exceeds limit {}",
                      u128_max_digits));
    REQUIRE(refused.error().bound_info().has_value());
    CHECK(refused.error().bound_info()->observed == u128_max);
    CHECK(refused.error().bound_info()->limit == u128_max);
}

TEST_CASE("a fraction of 65 significant digits that fits loads exactly", "[integration][wide]") {
    // 0.<the 65 digits of 5^92> is 5^27 / 2^65, within the bound, and the
    // factor reads back with its denominator past 64 bits.
    auto const digits = digits_of_five_to(92);
    REQUIRE(digits.size() == 65);
    auto client = ffi_client();
    auto const parsed = required(client.parse_dbc_text(
        std::stop_token{},
        wide_dbc_text("", std::format(" SG_ S : 0|8@1+ (0.{},0) [0|1] \"\" ECU\n", digits))));
    constexpr unsigned __int128 five_to_27 = 7'450'580'596'923'828'125;
    constexpr auto two_to_65 = static_cast<unsigned __int128>(1) << 65U;
    CHECK(parsed.dbc.messages.at(0).signals.at(0).factor.get() == ratio(five_to_27, two_to_65));
}

TEST_CASE("a multiplex value and value description keys at 2^128-1 load and read back exactly",
          "[integration][wide]") {
    // A 128-bit multiplexor selecting at 2^128-1, a 129-bit signed signal
    // describing -(2^128-1) and 2^128-1, and a value table keyed at both,
    // read from the load's reply and again from the formatted DBC.
    auto const tables =
        std::format("VAL_TABLE_ Extremes -{0} \"Below\" {0} \"Above\" ;\n\n", u128_max_digits);
    auto const body = std::format(" SG_ Mx M : 0|128@1+ (1,0) [0|{0}] \"\" ECU\n"
                                  " SG_ A m{0} : 128|8@1+ (1,0) [0|255] \"\" ECU\n"
                                  " SG_ Key : 136|129@1- (1,0) [-{0}|{0}] \"\" ECU\n\n"
                                  "VAL_ 256 Key -{0} \"Lowest\" {0} \"Highest\" ;\n",
                                  u128_max_digits);
    auto client = ffi_client();
    check_extremes(
        required(client.parse_dbc_text(std::stop_token{}, wide_dbc_text(tables, body))).dbc);
    check_extremes(required(client.format_dbc(std::stop_token{})));
}

TEST_CASE("a time bound of 2^64-1 microseconds reaches its limit", "[integration][wide]") {
    // The runtime the kernel's decisions run in comes up with a backend.
    auto const backend = required(make_ffi_backend(find_lib()));
    auto const bound = required(TimeBound::parse(std::format("{}", u64_max)));
    CHECK(bound == TimeBound{u64_max});
    auto const below = required(ltl::less_than(SignalName{"S"}, PhysicalValue{Rational{10, 1}}));
    CHECK(ltl::within(bound, ltl::atomic(below)).has_value());
    CHECK(ltl::always_within(bound, ltl::atomic(below)).has_value());
}

TEST_CASE("a time bound past the timestamp range is refused with its observed size at 128 bits",
          "[integration][wide]") {
    auto const backend = required(make_ffi_backend(find_lib()));
    constexpr auto two_to_64 = static_cast<unsigned __int128>(u64_max) + 1;
    auto const refused = TimeBound::parse(std::format("{}", two_to_64));
    REQUIRE_FALSE(refused.has_value());
    CHECK(refused.error().kind() == ErrorKind::InputBoundExceeded);
    CHECK(refused.error().message() ==
          std::format("time bound: rational component magnitude {} exceeds limit {}", two_to_64,
                      u64_max));
    REQUIRE(refused.error().bound_info().has_value());
    auto const& bound = *refused.error().bound_info();
    CHECK(bound.observed == two_to_64);
    CHECK(bound.limit == u64_max);
    CHECK(bound.field == "time bound");
}
