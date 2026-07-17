# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Aletheia environment (fish).  Source this file to make the verified shared
# library discoverable by every binding:
#
#     source /path/to/aletheia/env.fish
#
# It sets ALETHEIA_LIB to the ABSOLUTE path of libaletheia-ffi.so, resolved
# from this script's own location, so the value is correct no matter which
# directory you source it from.  The Python, C++, Go, and Rust bindings all
# read ALETHEIA_LIB at runtime to locate the library.
set -l _aletheia_here (path dirname (path resolve (status --current-filename)))
set -gx ALETHEIA_LIB "$_aletheia_here/lib/libaletheia-ffi.so"
