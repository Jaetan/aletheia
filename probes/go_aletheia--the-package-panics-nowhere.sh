#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/aletheia, against the claim docs/reference/GO_API.md makes about it.
# Claim: no call a host can make panics; every fallible call answers an error,
# which is what lets a host embed the binding and report a refusal rather than
# die of one. The package's own exception is the unlock of a lock nobody
# holds, which breaks an invariant of the unexported lock that only a defect
# inside the package can break, and the guide's error-handling section names
# it. So the probe holds three things: every panic outside the tests is that
# one, in the unexported method unlock and with the message
# TestClient_UnlockNotHeldFails in cancel_test.go expects; that panic
# is still there, so the guide's exception does not outlive the fault it
# names; and the guide still names it. The test files are not part of the
# claim; a test may panic to stop itself.
# Non-zero exit: a panic the guide does not name, the named one gone, or the
# guide no longer naming it. Exits 2 when the tree is not where this expects.
set -u
cd "$(dirname "$0")/.." || exit 2
[ -d go/aletheia ] || exit 2
guide=docs/reference/GO_API.md
[ -f "$guide" ] || exit 2

message='aletheia: unlock of a lock that is not held'
status=0

# Every panic outside the tests, as file:line:function:text, the function
# being the one whose header the line last passed.
panics=$(for f in go/aletheia/*.go; do
	case "$f" in *_test.go) continue ;; esac
	awk -v file="$f" '
		/^func / {
			name = $0
			sub(/^func +(\([^)]*\) *)?/, "", name)
			sub(/[^A-Za-z0-9_].*$/, "", name)
		}
		/panic\(/ { print file ":" NR ":" name ":" $0 }
	' "$f"
done)

named=$(printf '%s\n' "$panics" | grep -F ':unlock:' | grep -F "\"$message\"" || true)
others=$(printf '%s\n' "$panics" | grep -v -F ':unlock:' || true)
misworded=$(printf '%s\n' "$panics" | grep -F ':unlock:' | grep -v -F "\"$message\"" || true)

if [ -n "$others$misworded" ]; then
	echo "the package panics where the guide says it does not:"
	printf '%s\n' "$others" "$misworded" | sed '/^$/d; s/^/  /'
	status=1
fi
if [ -z "$named" ]; then
	echo "the unlock of a lock nobody holds no longer panics, and the guide still names that fault"
	status=1
fi
if ! grep -q 'unlock of a lock nobody holds' "$guide"; then
	echo "$guide no longer names the unlock of a lock nobody holds as the package's exception"
	status=1
fi

[ "$status" -eq 0 ] && echo "PASS: no call a host can make panics, and the guide names the package's own exception"
exit "$status"
