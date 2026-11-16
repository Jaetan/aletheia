// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// The 128-bit JSON reader and writer: nlohmann's own lexer, DOM builder and
// serializer, with a whole number past 64 bits held exactly.
#include "detail/wide_json.hpp"

#include <aletheia/limits.hpp>
#include <aletheia/types.hpp>

#include <nlohmann/json.hpp>

#include <algorithm>
#include <charconv>
#include <concepts>
#include <cstddef>
#include <cstdint>
#include <format>
#include <iterator>
#include <memory>
#include <optional>
#include <ranges>
#include <stdexcept>
#include <string>
#include <string_view>
#include <system_error>
#include <utility>
#include <vector>

namespace aletheia::detail {

// The binary node a negative number past -2^127 is held in: its subtype, and
// the bytes of its magnitude.
constexpr std::uint64_t wide_negative_subtype = 1;
constexpr std::size_t wide_negative_bytes = 16;
// The largest magnitude a negative signed 128-bit integer holds, 2^127.
constexpr unsigned __int128 signed_magnitude_max = static_cast<unsigned __int128>(1) << 127U;

// A magnitude's bytes, the least significant first.
static auto magnitude_bytes(unsigned __int128 magnitude) -> std::vector<std::uint8_t> {
    std::vector<std::uint8_t> bytes(wide_negative_bytes);
    for (auto& byte : bytes) {
        byte = static_cast<std::uint8_t>(magnitude);
        magnitude >>= 8U;
    }
    return bytes;
}

// The magnitude a binary node holds, or nullopt for any other node.
static auto wide_negative_magnitude(Json const& j) -> std::optional<unsigned __int128> {
    if (!j.is_binary())
        return std::nullopt;
    auto const& bytes = j.get_binary();
    // A node without a subtype answers 2^64-1 here.
    if (bytes.subtype() != wide_negative_subtype || bytes.size() != wide_negative_bytes)
        return std::nullopt;
    unsigned __int128 magnitude = bytes.at(bytes.size() - 1);
    for (auto const byte : bytes | std::views::reverse | std::views::drop(1))
        magnitude = (magnitude << 8U) | byte;
    return magnitude;
}

// The value of a run of decimal digits, or nullopt for text that is not one
// or a value past 2^128-1.
static auto digits_value(std::string_view digits) -> std::optional<unsigned __int128> {
    unsigned __int128 value = 0;
    auto const* const last = std::to_address(digits.end());
    auto const [ptr, ec] = std::from_chars(std::to_address(digits.begin()), last, value);
    if (ec != std::errc{} || ptr != last)
        return std::nullopt;
    return value;
}

namespace {

using DomBuilder =
    nlohmann::detail::json_sax_dom_parser<Json, nlohmann::detail::string_input_adapter_type>;

// The SAX handler `parse_json` reads with: every event goes on to nlohmann's
// DOM builder, which it holds, with two changes. An integer token past the
// lexer's 64-bit reads, which it hands over as a double with its text, is held
// as `Json` holds a whole number when its magnitude is at most 2^128-1. And
// every event is held to `max_nesting_depth`, counted as nlohmann's parse
// callback counts it: the containers open around a value, a key or a
// container's start.
class WideBuilder {
public:
    explicit WideBuilder(Json& root) : dom_(root) {}

    auto null() -> bool {
        within_bound(open_);
        return dom_.null();
    }

    auto boolean(bool value) -> bool {
        within_bound(open_);
        return dom_.boolean(value);
    }

    auto number_integer(Json::number_integer_t value) -> bool {
        within_bound(open_);
        return dom_.number_integer(value);
    }

    auto number_unsigned(Json::number_unsigned_t value) -> bool {
        within_bound(open_);
        return dom_.number_unsigned(value);
    }

    auto number_float(Json::number_float_t value, Json::string_t const& token) -> bool {
        auto const negative = token.starts_with('-');
        auto const magnitude = digits_value(std::string_view{token}.substr(negative ? 1 : 0));
        if (!magnitude) {
            within_bound(open_);
            return dom_.number_float(value, token);
        }
        if (!negative)
            return number_unsigned(magnitude.value());
        if (magnitude.value() <= signed_magnitude_max)
            return number_integer(static_cast<__int128>(0 - magnitude.value()));
        Json::binary_t node{magnitude_bytes(magnitude.value()), wide_negative_subtype};
        return binary(node);
    }

    auto string(Json::string_t& value) -> bool {
        within_bound(open_);
        return dom_.string(value);
    }

    auto binary(Json::binary_t& value) -> bool {
        within_bound(open_);
        return dom_.binary(value);
    }

    auto start_object(std::size_t length) -> bool {
        within_bound(open_++);
        return dom_.start_object(length);
    }

    auto key(Json::string_t& value) -> bool {
        within_bound(open_);
        return dom_.key(value);
    }

    auto end_object() -> bool {
        --open_;
        return dom_.end_object();
    }

    auto start_array(std::size_t length) -> bool {
        within_bound(open_++);
        return dom_.start_array(length);
    }

    auto end_array() -> bool {
        --open_;
        return dom_.end_array();
    }

    // The lexer's and the parser's refusals, which the DOM builder throws.
    template<typename Exception>
    auto parse_error(std::size_t position, std::string const& last_token, Exception const& ex)
        -> bool {
        return dom_.parse_error(position, last_token, ex);
    }

private:
    static void within_bound(std::size_t depth) {
        if (depth > max_nesting_depth)
            throw std::runtime_error("JSON nesting depth " + std::to_string(depth) +
                                     " exceeds limit " + std::to_string(max_nesting_depth));
    }

    DomBuilder dom_;
    std::size_t open_ = 0;
};

// Writes a value as `Json::dump` does, a binary node as its negative digits.
// The containers are walked here; every other value, and every key as the
// string it is, goes through nlohmann's serializer, which writes the escaping
// and refuses a string that is not UTF-8 exactly as `dump` does.
class WideWriter {
public:
    explicit WideWriter(int indent)
        : values_(nlohmann::detail::output_adapter<char, std::string>(out_), ' ')
        , pretty_(indent >= 0)
        , step_(static_cast<unsigned>(std::max(indent, 0))) {}

    // The text written so far.
    [[nodiscard]] auto text() && -> std::string { return std::move(out_); }

    void write(Json const& j) {
        if (auto const magnitude = wide_negative_magnitude(j)) {
            std::format_to(std::back_inserter(out_), "-{}", magnitude.value());
            return;
        }
        if (j.is_object() && !j.empty()) {
            write_members(j.get_ref<Json::object_t const&>(), '{', '}');
            return;
        }
        if (j.is_array() && !j.empty()) {
            write_members(j.get_ref<Json::array_t const&>(), '[', ']');
            return;
        }
        values_.dump(j, pretty_, false, step_, static_cast<unsigned>(margin_.size()));
    }

private:
    // One member per line, a step further in than the container, when pretty;
    // an object's member is its key and its value. The margin grows by the step
    // on the way in and shrinks by it on the way out, so no level's indentation
    // is computed from another's.
    template<typename Members>
    void write_members(Members const& members, char open, char close) {
        margin_.append(step_, ' ');
        out_ += open;
        for (auto const& [index, member] : std::views::enumerate(members)) {
            if (index > 0)
                out_ += ',';
            if (pretty_) {
                out_ += '\n';
                out_ += margin_;
            }
            if constexpr (std::same_as<Members, Json::object_t>) {
                values_.dump(Json(member.first), false, false, 0);
                out_ += pretty_ ? ": " : ":";
                write(member.second);
            } else {
                write(member);
            }
        }
        margin_.resize(margin_.size() - step_);
        if (pretty_) {
            out_ += '\n';
            out_ += margin_;
        }
        out_ += close;
    }

    // Declared before the serializer, which writes into it.
    std::string out_;
    nlohmann::detail::serializer<Json> values_;
    // The indentation of the members being written, when pretty.
    std::string margin_;
    bool pretty_;
    unsigned step_;
};

} // namespace

auto parse_json(std::string_view input) -> Json {
    Json root;
    WideBuilder builder{root};
    // The builder throws every refusal, so a parse that returns succeeded.
    Json::sax_parse(input, &builder);
    return root;
}

auto dump_json(Json const& j, int indent) -> std::string {
    WideWriter writer{indent};
    writer.write(j);
    return std::move(writer).text();
}

auto uint128_of(Json const& j) -> std::optional<unsigned __int128> {
    if (j.is_number_unsigned())
        return j.get<unsigned __int128>();
    if (j.is_number_integer() && j.get<__int128>() >= 0)
        return static_cast<unsigned __int128>(j.get<__int128>());
    return std::nullopt;
}

auto sign_magnitude_of(Json const& j) -> std::optional<SignMagnitude> {
    if (j.is_number_unsigned())
        return SignMagnitude{.negative = false, .magnitude = j.get<unsigned __int128>()};
    if (j.is_number_integer()) {
        auto const value = j.get<__int128>();
        auto const wide = static_cast<unsigned __int128>(value);
        return value < 0 ? SignMagnitude{.negative = true, .magnitude = 0 - wide}
                         : SignMagnitude{.negative = false, .magnitude = wide};
    }
    if (auto const magnitude = wide_negative_magnitude(j))
        return SignMagnitude{.negative = true, .magnitude = magnitude.value()};
    return std::nullopt;
}

auto json_of(bool negative, unsigned __int128 magnitude) -> Json {
    if (!negative || magnitude == 0)
        return magnitude;
    if (magnitude <= signed_magnitude_max)
        return static_cast<__int128>(0 - magnitude);
    return Json::binary(magnitude_bytes(magnitude), wide_negative_subtype);
}

auto json_of(SignMagnitude value) -> Json {
    return json_of(value.negative, value.magnitude);
}

} // namespace aletheia::detail
