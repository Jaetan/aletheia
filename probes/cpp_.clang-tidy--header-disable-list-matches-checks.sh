# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/.clang-tidy.
# Claim: the header comment that gives a reason for every disabled check names
# exactly the checks the Checks list disables, so neither list can drift from
# the other. Non-zero exit: a check disabled without a stated reason, or a
# reason for a check that is not disabled.
set -u
cd "$(dirname "$0")/.." || exit 2
file=cpp/.clang-tidy
disabled=$(sed -n '/^Checks: >/,/^$/p' "$file" | grep -oE '^\s*-[a-z][a-z0-9*-]*' | sed 's/^ *-//' | sort)
explained=$(sed -n '1,/^Checks: >/p' "$file" | grep -oE '(^#   |, )[a-z]+-[a-z0-9*-]+' | sed 's/^#   //; s/^, //' | sort -u)
diff <(printf '%s\n' "$disabled") <(printf '%s\n' "$explained")
