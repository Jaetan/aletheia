#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Aletheia environment (bash / zsh).  SOURCE this file — do not execute it —
# to make the verified shared library discoverable by every binding:
#
#     source /path/to/aletheia/env.sh
#
# It sets ALETHEIA_LIB to the ABSOLUTE path of libaletheia-ffi.so, resolved
# from this script's own location, so the value is correct no matter which
# directory you source it from.  The Python, C++, Go, and Rust bindings all
# read ALETHEIA_LIB at runtime to locate the library.
#
# Self-location needs bash's BASH_SOURCE or zsh's %x; POSIX sh (dash) cannot find
# a sourced script's path and would export a wrong ALETHEIA_LIB — fail loudly
# there instead of silently.  (fish users: source env.fish.)  The `${BASH_SOURCE:-}`
# probe has no array subscript, so it is safe to evaluate under dash.
if [ -z "${BASH_SOURCE:-}" ] && [ -z "${ZSH_VERSION:-}" ]; then
    echo "aletheia env.sh: source this from bash or zsh (fish users: source env.fish)." >&2
    return 1 2>/dev/null || exit 1
fi
# zsh: the %x prompt escape names the sourced file reliably even under
# NO_FUNCTION_ARGZERO (where $0 would be the shell name, resolving to the wrong
# directory); the eval hides the zsh-only syntax from bash's parser.  bash:
# BASH_SOURCE[0] is the sourced file.
if [ -n "${ZSH_VERSION:-}" ]; then
    eval '_aletheia_src="${(%):-%x}"'
else
    _aletheia_src="${BASH_SOURCE[0]:-$0}"
fi
_aletheia_here="$(cd "$(dirname "$_aletheia_src")" >/dev/null 2>&1 && pwd)"
export ALETHEIA_LIB="${_aletheia_here}/lib/libaletheia-ffi.so"
unset _aletheia_here _aletheia_src
