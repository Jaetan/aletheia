#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/include/aletheia/dbc.hpp.
# Claim: the header's opening sentence, that the definition embeds the
# vocabulary types, holds of every node-valued field and every message target.
# A node is a NodeName, and a message target names a validated CanId rather than
# a raw value beside a flag.
# Non-zero exit: a node-valued field is a bare string, or a target still carries
# the raw pair.
set -eu
root=$(git rev-parse --show-toplevel)
cd "$root"
header=cpp/include/aletheia/dbc.hpp
fail=0

# No target carries the raw pair any more.
if grep -nE '^\s+bool extended' "$header"; then
    echo "FAIL: a target still carries a raw extended flag beside its identifier"
    fail=1
fi

# Every field whose name says node is typed as one.
while IFS= read -r line; do
    case "$line" in
        *NodeName*) ;;
        *) echo "FAIL: a node-valued field is not a NodeName: $line"; fail=1 ;;
    esac
done <<EOD
$(grep -nE '^\s+(std::vector<)?[A-Za-z:_<>]+ (node|senders|receivers);' "$header"; \
  grep -nE 'struct DbcNode \{' -A2 "$header" | grep -E '^\S+-\s+\S+ name;')
EOD

[ "$fail" -eq 0 ] || exit 1
echo "PASS: node-valued fields and message targets carry their vocabulary types"
