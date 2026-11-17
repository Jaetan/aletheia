// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// The reply readers' one form of refusal, and the readers of each kind.
#include "detail/reply_shape.hpp"

#include "detail/bad_alloc.hpp"
#include "detail/kernel_value.hpp"
#include "detail/wide_json.hpp"

#include <aletheia/types.hpp>

#include <nlohmann/json.hpp>

#include <algorithm>
#include <cstdint>
#include <exception>
#include <initializer_list>
#include <optional>
#include <ranges>
#include <span>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace aletheia::detail {

auto ReplyPath::at(std::string_view key) const -> ReplyPath {
    ReplyPath place;
    place.text_ = text_.empty() ? std::string{key} : text_ + '/' + std::string{key};
    return place;
}

auto value_at(Json const& obj, std::string_view key) -> Json const* {
    return obj.contains(key) ? &obj.at(key) : nullptr;
}

auto holds_non_null(Json const& obj, std::string_view key) -> bool {
    if (auto const* const found = value_at(obj, key))
        return !found->is_null();
    return false;
}

auto json_kind(Json const& value) -> std::string_view {
    // nlohmann names every kind JSON text yields as JSON does.
    return value.is_binary() ? expect_number : value.type_name();
}

auto came(Json const& obj, std::string_view key) -> std::string_view {
    if (auto const* const found = value_at(obj, key))
        return json_kind(*found);
    return came_nothing;
}

// The string at `key`, nullptr when the key holds none.
static auto string_at(Json const& obj, std::string_view key) -> std::string const* {
    if (auto const* const found = value_at(obj, key))
        return found->is_string() ? &found->get_ref<std::string const&>() : nullptr;
    return nullptr;
}

auto came_word(Json const& obj, std::string_view key) -> std::string {
    if (auto const* const word = string_at(obj, key))
        return quote_json(*word);
    return std::string{came(obj, key)};
}

auto quote_json(std::string_view text) -> std::string {
    // nlohmann's ASCII-only writer escapes as Python's json.dumps does: the
    // two-character escapes, every other character below a space and every one
    // from DEL on as \u and four lowercase hex digits, a pair of them past
    // U+FFFF. A string the reader decoded is UTF-8; any other is written with
    // U+FFFD for each malformed sequence.
    return Json(std::string{text}).dump(-1, ' ', true, Json::error_handler_t::replace);
}

auto words(std::span<std::string_view const> expected) -> std::string {
    std::string out;
    for (auto const& [index, word] : std::views::enumerate(expected)) {
        if (index > 0)
            out += std::cmp_equal(index + 1, expected.size()) ? " or " : ", ";
        out += quote_json(word);
    }
    return out;
}

auto reply_refusal(ReplyPath const& path, std::string_view expected, std::string_view arrival)
    -> std::runtime_error {
    auto const where =
        path.text().empty() ? std::string{"reply"} : "reply " + std::string{path.text()};
    return std::runtime_error(where + ": expected " + std::string{expected} + ", got " +
                              std::string{arrival});
}

auto read_reply(std::string_view raw) -> Json {
    Json reply;
    try {
        reply = parse_json(raw);
    } catch (std::exception const& e) {
        rethrow_if_bad_alloc(e);
        throw reply_refusal(ReplyPath{}, expect_json_text, e.what());
    }
    if (!reply.is_object())
        throw reply_refusal(ReplyPath{}, expect_object, json_kind(reply));
    return reply;
}

auto read_object(Json const& value, ReplyPath const& path) -> Json const& {
    if (!value.is_object())
        throw reply_refusal(path, expect_object, json_kind(value));
    return value;
}

auto read_array(Json const& value, ReplyPath const& path) -> Json const& {
    if (!value.is_array())
        throw reply_refusal(path, expect_array, json_kind(value));
    return value;
}

auto read_string(Json const& value, ReplyPath const& path) -> std::string {
    if (!value.is_string())
        throw reply_refusal(path, expect_string, json_kind(value));
    return value.get<std::string>();
}

auto read_bool(Json const& value, ReplyPath const& path) -> bool {
    if (!value.is_boolean())
        throw reply_refusal(path, expect_boolean, json_kind(value));
    return value.get<bool>();
}

auto read_sign_magnitude(Json const& value, ReplyPath const& path) -> SignMagnitude {
    auto const whole = sign_magnitude_of(value);
    if (!whole)
        throw reply_refusal(path, expect_number, json_kind(value));
    return whole.value();
}

auto read_uint128(Json const& value, ReplyPath const& path) -> unsigned __int128 {
    auto const whole = read_sign_magnitude(value, path);
    if (whole.negative)
        throw reply_refusal(path, expect_number, json_kind(value));
    return whole.magnitude;
}

auto read_int64(Json const& value, ReplyPath const& path) -> std::int64_t {
    auto const narrow = read_sign_magnitude(value, path).to_int64();
    if (!narrow)
        throw reply_refusal(path, expect_number, json_kind(value));
    return narrow.value();
}

// The whole number at `key` of `obj`, nullopt when it holds none.
static auto whole_at(Json const& obj, std::string_view key) -> std::optional<SignMagnitude> {
    if (auto const* const found = value_at(obj, key))
        return sign_magnitude_of(*found);
    return std::nullopt;
}

auto read_rational(Json const& value, ReplyPath const& path) -> Rational {
    if (auto const whole = sign_magnitude_of(value))
        return KernelValue::rational(whole.value().negative, whole.value().magnitude, 1);
    // A value that is not an object holds neither key.
    auto const numerator = whole_at(value, "numerator");
    auto const denominator = whole_at(value, "denominator");
    if (numerator && denominator) {
        auto const& top = numerator.value();
        auto const& bottom = denominator.value();
        return KernelValue::rational(top.negative != bottom.negative && top.magnitude != 0,
                                     top.magnitude, bottom.magnitude);
    }
    throw reply_refusal(path, expect_rational, json_kind(value));
}

auto field_value(Json const& obj, ReplyPath const& path, std::string_view key,
                 std::string_view expected) -> Json const& {
    if (auto const* const found = value_at(obj, key))
        return *found;
    throw reply_refusal(path.at(key), expected, came_nothing);
}

auto field_object(Json const& obj, ReplyPath const& path, std::string_view key) -> Json const& {
    return field(obj, path, key, expect_object,
                 [](Json const& value, ReplyPath const& place) -> Json const& {
                     return read_object(value, place);
                 });
}

auto field_array(Json const& obj, ReplyPath const& path, std::string_view key) -> Json const& {
    return field(obj, path, key, expect_array,
                 [](Json const& value, ReplyPath const& place) -> Json const& {
                     return read_array(value, place);
                 });
}

auto field_string(Json const& obj, ReplyPath const& path, std::string_view key) -> std::string {
    return field(obj, path, key, expect_string, read_string);
}

auto field_bool(Json const& obj, ReplyPath const& path, std::string_view key) -> bool {
    return field(obj, path, key, expect_boolean, read_bool);
}

auto field_sign_magnitude(Json const& obj, ReplyPath const& path, std::string_view key)
    -> SignMagnitude {
    return field(obj, path, key, expect_number, read_sign_magnitude);
}

auto field_uint128(Json const& obj, ReplyPath const& path, std::string_view key)
    -> unsigned __int128 {
    return field(obj, path, key, expect_number, read_uint128);
}

auto field_int64(Json const& obj, ReplyPath const& path, std::string_view key) -> std::int64_t {
    return field(obj, path, key, expect_number, read_int64);
}

auto field_rational(Json const& obj, ReplyPath const& path, std::string_view key) -> Rational {
    return field(obj, path, key, expect_rational, read_rational);
}

auto field_word(Json const& obj, ReplyPath const& path, std::string_view key,
                std::initializer_list<std::string_view> expected) -> std::string_view {
    if (auto const* const word = string_at(obj, key)) {
        auto const* const match = std::ranges::find(expected, *word);
        if (match != expected.end())
            return *match;
    }
    throw reply_refusal(path.at(key), words(expected), came_word(obj, key));
}

auto status_word(ReplyStatus status) -> std::string_view {
    switch (status) {
    case ReplyStatus::Success:
        return "success";
    case ReplyStatus::Validation:
        return "validation";
    case ReplyStatus::Complete:
        return "complete";
    case ReplyStatus::Ack:
        return "ack";
    case ReplyStatus::Error:
        return "error";
    }
    throw std::logic_error("unnamed reply status");
}

auto field_status(Json const& obj, ReplyPath const& path, std::string_view key,
                  std::initializer_list<ReplyStatus> expected) -> ReplyStatus {
    if (auto const* const word = string_at(obj, key)) {
        auto const* const match = std::ranges::find(expected, *word, status_word);
        if (match != expected.end())
            return *match;
    }
    auto const spellings =
        expected | std::views::transform(status_word) | std::ranges::to<std::vector>();
    throw reply_refusal(path.at(key), words(spellings), came_word(obj, key));
}

} // namespace aletheia::detail
