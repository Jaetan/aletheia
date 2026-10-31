// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
// What the JSON response parsers and the DBC parsers share: the table lookup,
// and the DBC decoder json_parse_dbc.cpp defines for the replies carrying one.
#pragma once

#include <aletheia/dbc.hpp>

#include "wide_json.hpp"

#include <optional>
#include <string_view>

namespace aletheia {

// The value of a table entry, or nullopt when the table has no such entry.
// Every string-to-enum table the JSON parsers keep is an array scanned
// linearly, which is fine on these cold paths.
template<typename Table>
auto lookup(Table const& table, std::string_view wire)
    -> std::optional<typename Table::value_type::second_type> {
    for (auto const& [name, value] : table)
        if (name == wire)
            return value;
    return std::nullopt;
}

} // namespace aletheia

namespace aletheia::detail {

// The DBC object of a reply, at "dbc", each place refused as
// detail/reply_shape.hpp refuses it.
auto parse_dbc_definition(Json const& dbc) -> DbcDefinition;

} // namespace aletheia::detail
