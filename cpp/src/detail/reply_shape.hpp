// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The refusal every reply reader throws for a place holding what the kernel
// never writes there reads "reply <path>: expected <what>, got <what came>",
// the same text in the four bindings. The path is the reply proof's: the keys
// from the reply's root joined by "/", an array's entries keeping the array's
// path, the whole reply's path empty ("reply: expected object, got array").
// What is expected and what came are JSON kinds, "string", "boolean",
// "number", "array", "object" or "null", and a key the reply lacks came as
// "nothing". A rational place expects "a rational": a number, or the
// {numerator, denominator} object the kernel writes a fraction as. A place
// holding one of a set of words expects them quoted, and a string outside them
// came quoted; an issue's code expects "an issue code" and an error reply's
// "an error code", a string outside the table came quoted. A whole-number
// place expects a "number" written as digits, all the kernel writes there.
//
// A reader narrows each place itself and builds its refusal here: `came`
// names what a key held, `json_kind` what a value is, `came_word` what a word
// place held. Every refusal is a std::runtime_error whose text is the
// refusal's, which the response parsers answer as a Protocol error.

#pragma once

#include <aletheia/types.hpp>

#include "wide_json.hpp"

#include <array>
#include <concepts>
#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <limits>
#include <ranges>
#include <span>
#include <stdexcept>
#include <string>
#include <string_view>
#include <type_traits>
#include <utility>
#include <vector>

namespace aletheia::detail {

// A place in a reply: its keys from the root joined by "/", empty for the
// whole reply.
class ReplyPath {
public:
    // The place of `key` in the object at this place.
    [[nodiscard]] auto at(std::string_view key) const -> ReplyPath;

    [[nodiscard]] auto text() const -> std::string_view { return text_; }

private:
    std::string text_;
};

// What a place holds: a JSON kind, a rational, or JSON text for a whole reply.
inline constexpr std::string_view expect_string = "string";
inline constexpr std::string_view expect_boolean = "boolean";
inline constexpr std::string_view expect_number = "number";
inline constexpr std::string_view expect_array = "array";
inline constexpr std::string_view expect_object = "object";
inline constexpr std::string_view expect_rational = "a rational";
inline constexpr std::string_view expect_json_text = "JSON text";
inline constexpr std::string_view expect_issue_code = "an issue code";
inline constexpr std::string_view expect_error_code = "an error code";

// What came at a key the reply lacks.
inline constexpr std::string_view came_nothing = "nothing";

// The value at `key` of `obj`, nullptr when it holds none there. A value that
// is not an object holds no key.
[[nodiscard]] auto value_at(Json const& obj, std::string_view key) -> Json const*;

// Whether `key` of `obj` holds a value other than null.
[[nodiscard]] auto holds_non_null(Json const& obj, std::string_view key) -> bool;

// The JSON kind of a value: a negative number past -2^127, which `Json` holds
// as a binary node, is a number.
[[nodiscard]] auto json_kind(Json const& value) -> std::string_view;

// What `key` held in the object `obj`: its value's JSON kind, or nothing.
[[nodiscard]] auto came(Json const& obj, std::string_view key) -> std::string_view;

// What a word place held: its string quoted, another value's kind, or nothing.
[[nodiscard]] auto came_word(Json const& obj, std::string_view key) -> std::string;

// `text` as a JSON string with every character past ASCII escaped, DEL
// included, the quoting the other bindings print a word in, so a string
// outside a place's words reads alike in all four.
[[nodiscard]] auto quote_json(std::string_view text) -> std::string;

// A word place's words quoted: "a", "a" or "b", "a", "b" or "c".
[[nodiscard]] auto words(std::span<std::string_view const> expected) -> std::string;

// The refusal of a reply place.
[[nodiscard]] auto reply_refusal(ReplyPath const& path, std::string_view expected,
                                 std::string_view arrival) -> std::runtime_error;

// The object a kernel reply's text holds. Text that is not one JSON value is
// refused as JSON text expected, naming the reader's reason, and a value that
// is not an object by its kind.
[[nodiscard]] auto read_reply(std::string_view raw) -> Json;

// The readers of the value at a place, each refusing a value of another kind.
// A whole number is written as digits; a number with a fraction or an
// exponent, or past 2^128-1, is refused as the number it does not hold.

// The object and the array readers answer the value they are given, so a
// temporary, which would leave the answer dangling, is refused at compile time.
[[nodiscard]] auto read_object(Json const& value, ReplyPath const& path) -> Json const&;
auto read_object(Json&& value, ReplyPath const& path) -> Json const& = delete;
[[nodiscard]] auto read_array(Json const& value, ReplyPath const& path) -> Json const&;
auto read_array(Json&& value, ReplyPath const& path) -> Json const& = delete;
[[nodiscard]] auto read_string(Json const& value, ReplyPath const& path) -> std::string;
[[nodiscard]] auto read_bool(Json const& value, ReplyPath const& path) -> bool;
[[nodiscard]] auto read_sign_magnitude(Json const& value, ReplyPath const& path) -> SignMagnitude;
// A whole number at a place the kernel proves natural.
[[nodiscard]] auto read_uint128(Json const& value, ReplyPath const& path) -> unsigned __int128;
// A whole number at a place whose proven range an int64 holds, an attribute's
// integer value or bound.
[[nodiscard]] auto read_int64(Json const& value, ReplyPath const& path) -> std::int64_t;
// A number or its {numerator, denominator} object. The object's sign is the
// quotient's, so a negative denominator, which the kernel never writes, flips
// it as the other bindings' readers do; a zero denominator, which it never
// writes either, is stored as written.
[[nodiscard]] auto read_rational(Json const& value, ReplyPath const& path) -> Rational;

// A whole number at a natural place read into its own type `T`: the kernel
// proves the range `T` holds, so a number past it is refused as the number the
// place does not hold.
template<std::unsigned_integral T>
[[nodiscard]] auto read_unsigned(Json const& value, ReplyPath const& path) -> T {
    auto const wide = read_uint128(value, path);
    if (wide > std::numeric_limits<T>::max())
        throw reply_refusal(path, expect_number, json_kind(value));
    return static_cast<T>(wide);
}

// The value at `key` of the object `obj` at `path`, an absent key refused as
// nothing came, `expected` being what the place expects.
[[nodiscard]] auto field_value(Json const& obj, ReplyPath const& path, std::string_view key,
                               std::string_view expected) -> Json const&;

// The key `key` of the object `obj` at `path`, read with `read`, which names
// its own expectation for a value of the wrong kind; an absent key is refused
// as nothing came, `expected` being what `read` expects.
template<typename Read>
[[nodiscard]] auto field(Json const& obj, ReplyPath const& path, std::string_view key,
                         std::string_view expected, Read read) -> decltype(auto) {
    return read(field_value(obj, path, key, expected), path.at(key));
}

// The fields of each kind, each refusing an absent key as nothing came.

[[nodiscard]] auto field_object(Json const& obj, ReplyPath const& path, std::string_view key)
    -> Json const&;
[[nodiscard]] auto field_array(Json const& obj, ReplyPath const& path, std::string_view key)
    -> Json const&;
[[nodiscard]] auto field_string(Json const& obj, ReplyPath const& path, std::string_view key)
    -> std::string;
[[nodiscard]] auto field_bool(Json const& obj, ReplyPath const& path, std::string_view key) -> bool;
[[nodiscard]] auto field_sign_magnitude(Json const& obj, ReplyPath const& path,
                                        std::string_view key) -> SignMagnitude;
[[nodiscard]] auto field_uint128(Json const& obj, ReplyPath const& path, std::string_view key)
    -> unsigned __int128;
[[nodiscard]] auto field_int64(Json const& obj, ReplyPath const& path, std::string_view key)
    -> std::int64_t;
[[nodiscard]] auto field_rational(Json const& obj, ReplyPath const& path, std::string_view key)
    -> Rational;

template<std::unsigned_integral T>
[[nodiscard]] auto field_unsigned(Json const& obj, ReplyPath const& path, std::string_view key)
    -> T {
    return field(obj, path, key, expect_number, read_unsigned<T>);
}

// The object at `key`, read with `read` at the key's place.
template<typename Read>
[[nodiscard]] auto field_object_of(Json const& obj, ReplyPath const& path, std::string_view key,
                                   Read read) {
    return read(field_object(obj, path, key), path.at(key));
}

// The array at `key`, each entry an object read with `read` at the array's
// place.
template<typename Read>
[[nodiscard]] auto field_objects(Json const& obj, ReplyPath const& path, std::string_view key,
                                 Read read)
    -> std::vector<std::invoke_result_t<Read&, Json const&, ReplyPath const&>> {
    auto const place = path.at(key);
    std::vector<std::invoke_result_t<Read&, Json const&, ReplyPath const&>> out;
    for (auto const& entry : field_array(obj, path, key))
        out.push_back(read(read_object(entry, place), place));
    return out;
}

// The array at `key`, each entry a string, as the string type `T` of its
// place.
template<typename T>
[[nodiscard]] auto field_strings(Json const& obj, ReplyPath const& path, std::string_view key)
    -> std::vector<T> {
    auto const place = path.at(key);
    auto const& entries = field_array(obj, path, key);
    std::vector<T> out;
    out.reserve(entries.size());
    for (auto const& entry : entries)
        out.emplace_back(read_string(entry, place));
    return out;
}

// The word at `key`, one of `expected`, any other refused with the words
// quoted. A place of one word reads it only to refuse another, so the word
// returned may be dropped.
auto field_word(Json const& obj, ReplyPath const& path, std::string_view key,
                std::initializer_list<std::string_view> expected) -> std::string_view;

// The words a tag place holds, each paired with the member it reads as.
template<typename Member, std::size_t N>
using WordTable = std::array<std::pair<std::string_view, Member>, N>;

// The member `table` pairs with the word at `key`, nullptr when the key holds
// no word the table names.
template<typename Member, std::size_t N>
[[nodiscard]] auto member_at(Json const& obj, std::string_view key,
                             WordTable<Member, N> const& table) -> Member const* {
    auto const* const value = value_at(obj, key);
    if (value == nullptr || !value->is_string())
        return nullptr;
    std::string_view const word = value->get_ref<std::string const&>();
    for (auto const& [name, member] : table)
        if (name == word)
            return &member;
    return nullptr;
}

// The member `table` pairs with the word at `key`, any other refused as
// `expected`, a string outside the table quoted as `field_word` quotes it.
template<typename Member, std::size_t N>
[[nodiscard]] auto field_member(Json const& obj, ReplyPath const& path, std::string_view key,
                                WordTable<Member, N> const& table, std::string_view expected)
    -> Member {
    if (auto const* const member = member_at(obj, key, table))
        return *member;
    throw reply_refusal(path.at(key), expected, came_word(obj, key));
}

// The member `table` pairs with the word at `key`, any other refused with the
// table's words quoted as `field_word` refuses them.
template<typename Member, std::size_t N>
[[nodiscard]] auto field_member(Json const& obj, ReplyPath const& path, std::string_view key,
                                WordTable<Member, N> const& table) -> Member {
    if (auto const* const member = member_at(obj, key, table))
        return *member;
    auto const spellings = table | std::views::keys | std::ranges::to<std::vector>();
    throw reply_refusal(path.at(key), words(spellings), came_word(obj, key));
}

// The status at a reply's root: the answer each command awaits, and the error
// any command may answer.
enum class ReplyStatus : std::uint8_t { Success, Validation, Complete, Ack, Error };

// The word the kernel writes for `status`.
[[nodiscard]] auto status_word(ReplyStatus status) -> std::string_view;

// The status at `key`, one of `expected`, any other refused with the words
// quoted as `field_word` refuses them. It is the one reader of a status's
// word; a reply that may only be an error reads it to refuse another, so the
// status returned may be dropped.
auto field_status(Json const& obj, ReplyPath const& path, std::string_view key,
                  std::initializer_list<ReplyStatus> expected) -> ReplyStatus;

} // namespace aletheia::detail
