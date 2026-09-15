# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes cpp/.clang-tidy, cpp/tests/.clang-tidy and cpp/tests/fuzz/.clang-tidy.
# Claim: in each of the three configurations the header comment that gives a
# reason for every disabled check names exactly the checks the Checks list
# disables, so neither list can drift from the other. Non-zero exit: a check
# disabled without a stated reason, or a reason for a check that is not
# disabled.
set -u
cd "$(dirname "$0")/.." || exit 2
status=0
for file in cpp/.clang-tidy cpp/tests/.clang-tidy cpp/tests/fuzz/.clang-tidy; do
    disabled=$(sed -n '/^Checks: >/,/^$/p' "$file" \
        | grep -oE '^\s*-[a-z][A-Za-z0-9*.-]*' | sed 's/^ *-//' | sort)
    explained=$(sed -n '1,/^Checks: >/p' "$file" \
        | grep -oE '(^#   |, )[a-z]+-[A-Za-z0-9*.-]+' | sed 's/^#   //; s/^, //' | sort -u)
    if ! diff <(printf '%s\n' "$disabled") <(printf '%s\n' "$explained"); then
        echo "the two lists disagree in $file"
        status=1
    fi
done
exit $status
