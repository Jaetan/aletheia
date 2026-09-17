#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Probes python/aletheia/client/_backend.py.
# Claim: where the module header says what the other two bindings pass for a
# session's state, it names the type each of their interfaces takes. The header
# said C++ passes a void pointer long after that binding moved to an owning
# handle, and nothing noticed: a sentence about another binding is read by
# nobody who is looking at that binding.
# The two type names are read from the two interfaces rather than written here.
# Non-zero exit: the header names a type its subject's interface does not take.
# Exits 2 when a source is not where this expects it.
set -u
cd "$(dirname "$0")/.." || exit 2
header=python/aletheia/client/_backend.py
cpp=cpp/include/aletheia/backend.hpp
go=go/aletheia/backend.go
for f in "$header" "$cpp" "$go"; do
	[ -f "$f" ] || exit 2
done

# The first parameter of each interface's process method.
cpp_type=$(grep -oE "process\(const [A-Za-z_]+&" "$cpp" | head -1 | sed 's/process(const //; s/&//')
go_type=$(grep -oE "Process\(state [a-z]+\.[A-Za-z]+" "$go" | head -1 | sed 's/Process(state //')
[ -n "$cpp_type" ] || { echo "the C++ interface's process method was not read"; exit 2; }
[ -n "$go_type" ] || { echo "the Go interface's Process method was not read"; exit 2; }

# The header's own paragraph about the state, up to the end of the docstring.
paragraph=$(sed -n "/A session's state is an/,/\"\"\"/p" "$header")
[ -n "$paragraph" ] || { echo "the header no longer has a paragraph about the state"; exit 2; }

status=0
if ! grep -q "$cpp_type" <<< "$paragraph"; then
	echo "the header does not name $cpp_type, which is what the C++ interface takes"
	status=1
fi
if ! grep -q "$go_type" <<< "$paragraph"; then
	echo "the header does not name $go_type, which is what the Go interface takes"
	status=1
fi
if grep -qE "C\+\+ ``void\*``|C\+\+ .void \*." <<< "$paragraph"; then
	echo "the header says C++ passes a void pointer, and its interface takes $cpp_type"
	status=1
fi

[ "$status" -eq 0 ] || exit 1
echo "PASS: the header names $go_type and $cpp_type, which is what the two interfaces take"
