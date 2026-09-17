#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes go/excel/excel_test.go.
# Claim: the library search this module's tests carry is the binding's own: the
# same environment variable first, then the same relative candidates in the same
# order. The binding's has one step this one does not, the path a backend
# registered, and that step is allowed to sit between the two.
#
# The two cannot be one. go/excel is a module of its own, so it reaches the
# binding's exported surface and nothing else, and the binding's search is
# unexported: what the tests inside the binding's own module now share through
# the test-only re-export is out of this module's reach. So the duplication is
# structural and this probe holds the copy in step with the original.
# Non-zero exit: the two orders differ. Exits 2 when a file has moved.
set -u
cd "$(dirname "$0")/.." || exit 2
test_file=go/excel/excel_test.go
renderer=go/aletheia/renderer.go

# The candidate list of one function, in order: the string literals ending in
# libaletheia-ffi.so between the function header and its closing brace.
search_order() {
	awk -v fn="$2" '
		$0 ~ "^func " fn "\\(" { inside = 1 }
		inside && /ALETHEIA_LIB/ { print "env:ALETHEIA_LIB" }
		inside && /"[^"]*libaletheia-ffi\.so"/ {
			line = $0
			while (match(line, /"[^"]*libaletheia-ffi\.so"/)) {
				print "candidate:" substr(line, RSTART + 1, RLENGTH - 2)
				line = substr(line, RSTART + RLENGTH)
			}
		}
		inside && /^}/ { exit }
	' "$1"
}

from_test=$(search_order "$test_file" findFFILib)
from_renderer=$(search_order "$renderer" findFFILibrary)

if [ -z "$from_test" ] || [ -z "$from_renderer" ]; then
	echo "one of the two search functions was not found; the probe is naming the wrong file"
	exit 1
fi

if [ "$from_test" = "$from_renderer" ]; then
	echo "PASS: both searches read"
	printf '%s\n' "$from_test" | sed 's/^/  /'
	exit 0
fi

echo "the two library searches differ"
echo "--- $test_file findFFILib"
printf '%s\n' "$from_test" | sed 's/^/  /'
echo "--- $renderer findFFILibrary"
printf '%s\n' "$from_renderer" | sed 's/^/  /'
exit 1
