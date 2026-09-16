#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/include/aletheia/dbc.hpp.
# Claim: DbcDefinition's data members are the Agda DBC record's fields, in
# the record's order, under the snake_case spelling of each camelCase name,
# with no exception: every field maps mechanically. The Agda record is read from
# src/Aletheia/DBC/Types.agda; the C++ members are the non-function,
# non-cache declarations of struct DbcDefinition. Non-zero exit: the two
# lists differ anywhere else, or the exception is gone (rename the member and
# drop it here).
set -u
cd "$(dirname "$0")/.." || exit 2
agda=$(sed -n '/^record DBC : Set where/,/^$/p' src/Aletheia/DBC/Types.agda \
    | grep -E '^    [a-zA-Z]+ :' | sed -E 's/^    ([a-zA-Z]+) :.*/\1/' \
    | sed -E 's/([A-Z])/_\L\1/g')
cpp=$(sed -n '/^struct DbcDefinition {/,/^};/p' cpp/include/aletheia/dbc.hpp \
    | grep -E '^    (std::string|std::vector<[A-Za-z]+>) [a-z_]+;' \
    | sed -E 's/^    [^ ]+ ([a-z_]+);.*/\1/')
diff <(printf '%s\n' "$agda") <(printf '%s\n' "$cpp")
