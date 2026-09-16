#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/.clang-format.
# Claim: every option key the file sets is a key clang-format 22 still knows
# under that name, so no option rides on a deprecated alias that a later
# clang-format can drop silently, changing the enforced style without a diff
# in this file. Non-zero exit: at least one key is absent from the tool's own
# canonical dump of the same configuration (BasedOnStyle is a directive, not a
# dumped option, and is skipped).
set -u
cd "$(dirname "$0")/.." || exit 2
dump=$(cd cpp && clang-format-22 --dump-config) || exit 2
status=0
while IFS= read -r key; do
    [ "$key" = "BasedOnStyle" ] && continue
    if ! printf '%s\n' "$dump" | grep -q "^$key:"; then
        echo "deprecated or unknown key: $key"
        status=1
    fi
done < <(grep -E '^[A-Za-z0-9]+:' cpp/.clang-format | cut -d: -f1)
exit $status
