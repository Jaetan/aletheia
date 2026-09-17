#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia/doc.go.
# Claim: what the package documentation cites exists: the two contract
# documents, the section of PROTOCOL.md it names, the Agda module and the
# proof it names for the streaming obligation, the four functional options
# and the two constructors its examples call, and the three verdicts it
# links. Non-zero exit: a citation resolves nowhere.
set -u
cd "$(dirname "$0")/.." || exit 2
f=go/aletheia/doc.go
status=0
for d in docs/architecture/CANCELLATION.md docs/architecture/PROTOCOL.md docs/LOG_EVENTS.yaml; do
    grep -q "$d" "$f" || { echo "doc.go no longer cites $d; retire this line"; status=1; continue; }
    [ -f "$d" ] || { echo "$d is cited and missing"; status=1; }
done
section=$(grep -o '"Streaming Semantics: [^"]*"' "$f" | tr -d '"')
[ -n "$section" ] || { echo "no PROTOCOL.md section named"; status=1; }
[ -z "$section" ] || grep -q "^### $section" docs/architecture/PROTOCOL.md || { echo "PROTOCOL.md has no section $section"; status=1; }
module=$(grep -o 'Aletheia\.Protocol\.Adequacy\.[A-Za-z]*' "$f" | head -1)
[ -f "src/$(printf '%s' "$module" | tr . /).agda" ] || { echo "Agda module $module is missing"; status=1; }
grep -q "streaming-warms-cache" "src/$(printf '%s' "$module" | tr . /).agda" || { echo "streaming-warms-cache is not in $module"; status=1; }
for fn in $(grep -o 'aletheia\.[A-Z][A-Za-z]*(' "$f" | tr -d '(' | cut -d. -f2 | sort -u); do
    grep -q "^func $fn(\|^func (c \*Client) $fn(" go/aletheia/*.go || { echo "aletheia.$fn is called in the examples and declared nowhere"; status=1; }
done
for v in Unresolved Holds Fails; do
    grep -q "\[$v\]" "$f" || continue
    grep -qP "^\t$v\b" go/aletheia/result.go || { echo "[$v] is linked and not a Verdict constant"; status=1; }
done
[ "$status" -eq 0 ] && echo "PASS: every citation in doc.go resolves"
exit $status
