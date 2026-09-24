#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes docs/development/BUILDING.md as the owner of the dependency ledger.
# Claim: the ledger has one home, the guide's Dependencies and Licenses
# section: no DEPENDENCIES.md is tracked, and no tracked file outside the
# changelog (which records the move) names one, so every reader is sent to
# the section. This probe is excluded from the sweep, since it names the file
# to look for it.
# Non-zero exit: a DEPENDENCIES.md is tracked, or a tracked file names one.
set -u
cd "$(dirname "$0")/.." || exit 2
status=0
if git ls-files --error-unmatch DEPENDENCIES.md > /dev/null 2>&1; then
    echo "DEPENDENCIES.md is tracked beside the guide's ledger"; status=1
fi
grep -q '^## Dependencies and Licenses$' docs/development/BUILDING.md || { echo "the guide has no Dependencies and Licenses section"; status=1; }
hits=$(git grep -n 'DEPENDENCIES\.md' -- . ':!CHANGELOG.md' ":!$0" 2>/dev/null)
[ -z "$hits" ] || { echo "tracked files still name DEPENDENCIES.md:"; printf '%s\n' "$hits" | sed 's/^/  /'; status=1; }
[ "$status" -eq 0 ] && echo "PASS: the ledger has one home and nothing tracked names the old file"
exit "$status"
