#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/include/aletheia/validation.hpp and cpp/include/aletheia/client.hpp.
# Claim: the strictness contract of format_dbc_text is stated once, on the
# method that has it, and the struct it returns points there instead of
# restating it. Non-zero exit: the method's header stops stating the
# contract, or the struct's header states it again.
set -u
cd "$(dirname "$0")/.." || exit 2
status=0
client=cpp/include/aletheia/client.hpp
validation=cpp/include/aletheia/validation.hpp

grep -q 'provably re-parses to the input DBC' "$client" || {
    echo "the method's header no longer states the round-trip contract"
    status=1
}
grep -q 'ErrorKind::TextRoundtrip' "$client" || {
    echo "the method's header no longer names the refusal kind"
    status=1
}
for restated in 'always strict' 'provably re-parses' 'ErrorKind::TextRoundtrip'; do
    grep -q "$restated" "$validation" && {
        echo "the struct's header restates the contract: $restated"
        status=1
    }
done
grep -q 'stated on format_dbc_text in client.hpp' "$validation" || {
    echo "the struct's header does not point at the contract's owner"
    status=1
}
exit $status
