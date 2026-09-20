#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes .github/workflows/*.yml.
# Claim: the documentation exemption is one set of paths wherever it is written,
# no workflow carrying it defines a context the branch ruleset requires, and the
# two lanes it exists for, reproducible-build and the stability bench, are in a
# file that carries it.  A path filter skips every job of its workflow, so a
# required context in a filtered file is one no run can clear, and a lane the
# filter was written for that sits in an unfiltered file pays its whole
# toolchain to decide it has nothing to do.
# Read with awk rather than a YAML loader, so this says the same thing as
# python/tests/test_doc_only_path_exemption.py by another instrument.
# Non-zero exit: the lists disagree, a required context is behind a filter, or
# an exempt lane is not.
set -u
cd "$(dirname "$0")/.." || exit 2
status=0

# The contexts the `main` ruleset requires; GitHub keeps the ruleset outside the
# tree (docs/development/BRANCH_PR_HYGIENE.md).
required_a='tools/run_ci.py (all gates)'
required_b='mutation testing'

# One list per `paths-ignore:` block: the block's own indented items, joined,
# printed with the file it was read from.
lists=$(for wf in .github/workflows/*.yml; do
    awk -v wf="$wf" '
        /^ *paths-ignore: *$/ { collecting = 1; items = ""; next }
        collecting && /^ *- / { gsub(/^ *- |[[:space:]]*$/, ""); items = items " " $0; next }
        collecting { print wf ":" items; collecting = 0 }
        END { if (collecting) print wf ":" items }
    ' "$wf"
done)
[ -n "$lists" ] || { echo "no workflow carries a documentation exemption"; exit 1; }

distinct=$(printf '%s\n' "$lists" | sed 's/^[^:]*://' | sort -u)
[ "$(printf '%s\n' "$distinct" | wc -l)" -eq 1 ] || {
    echo "the ignored-path lists disagree:"
    printf '%s\n' "$lists" | sed 's/^/  /'
    status=1
}

filtered=$(printf '%s\n' "$lists" | sed 's/:.*//' | sort -u)
for wf in $filtered; do
    for context in "$required_a" "$required_b"; do
        grep -qF "name: $context" "$wf" && {
            echo "$wf is path-filtered and defines the required context '$context'"
            status=1
        }
    done
done

for lane in 'reproducible-build' 'stability bench (advisory)'; do
    home=$(grep -lF "name: $lane" .github/workflows/*.yml)
    case $home in
        '') echo "no workflow defines the lane '$lane'"; status=1; continue ;;
        *$'\n'*) echo "more than one workflow defines the lane '$lane'"; status=1; continue ;;
    esac
    printf '%s\n' "$filtered" | grep -qxF "$home" || {
        echo "'$lane' is in $home, which carries no documentation exemption"
        status=1
    }
done

# A filter on one event and not the other leaves half the cost standing, so
# every event a diff reaches these lanes by carries it.  workflow_dispatch takes
# no path filter and is the manual escape hatch.
for wf in $filtered; do
    events=$(awk '/^on: *$/ { reading = 1; next }
                  reading && /^[a-z]/ { reading = 0 }
                  reading && /^  [a-z_]+: *$/ { gsub(/[: ]/, ""); print }' "$wf")
    for event in $events; do
        [ "$event" = "workflow_dispatch" ] && continue
        awk -v want="  $event:" '
            $0 == want { reading = 1; next }
            reading && /^  [a-z]/ { reading = 0 }
            reading && /^ *paths-ignore: *$/ { found = 1 }
            END { exit !found }
        ' "$wf" || {
            echo "$wf runs on $event with no documentation exemption"
            status=1
        }
    done
done

[ "$status" -eq 0 ] && echo "PASS: one exemption, no required context behind it, both exempt lanes under it"
exit "$status"
