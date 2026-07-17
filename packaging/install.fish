#!/usr/bin/env fish
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Aletheia installer (fish).  Prints how to wire the bundled library and
# language bindings into your shell and toolchain.  It does NOT edit your
# config.fish (or ~/.bashrc / ~/.zshrc) — you stay in control; it prints the
# exact line to add.

set -l here (path dirname (path resolve (status --current-filename)))
set -l lib "$here/lib/libaletheia-ffi.so"

if not test -f "$lib"
    printf 'error: %s not found — run this from the unpacked aletheia bundle.\n' "$lib" >&2
    exit 1
end

# Defense-in-depth: the Python loader rejects a group/world-writable .so.
# `cp`/`tar` preserve owner-write-only permissions (0644/0755), so this is
# normally a no-op; it hardens against an unpack that widened the mode.  The
# glob always matches — the guard above guarantees at least the main .so.
chmod go-w $here/lib/*.so*

printf '%s\n' \
  "Aletheia is unpacked at:" \
  "  $here" \
  "" \
  "----------------------------------------------------------------------" \
  "1. Make the library discoverable (sets ALETHEIA_LIB).  Add the matching" \
  "   line to your shell startup file, or run it now for this shell only:" \
  "" \
  "     fish         (~/.config/fish/config.fish):" \
  "       source $here/env.fish" \
  "" \
  "     bash / zsh   (~/.bashrc or ~/.zshrc):" \
  "       source $here/env.sh" \
  "" \
  "----------------------------------------------------------------------" \
  "2. Use Aletheia from your language (each reads ALETHEIA_LIB at runtime):" \
  "" \
  "   Python  (requires Python 3.14+; no third-party runtime dependencies):" \
  "     # In a virtual environment you have created and activated:" \
  "     pip install $here/bindings/python" \
  "     # Or, with no venv (works on an externally-managed / PEP 668 Python)," \
  "     # install into an isolated directory and put it on PYTHONPATH:" \
  "     pip install --target ~/.local/lib/aletheia $here/bindings/python" \
  "     export PYTHONPATH=~/.local/lib/aletheia" \
  "     python -c 'import aletheia; from aletheia import FFIBackend; FFIBackend()'" \
  "" \
  "   C++  (CMake; fetches nlohmann/json + yaml-cpp + OpenXLSX at configure time):" \
  "     # in your project's CMakeLists.txt:" \
  "     add_subdirectory($here/bindings/cpp aletheia-cpp)" \
  "     target_link_libraries(your_app PRIVATE aletheia::aletheia-cpp)" \
  "" \
  "   Go  (in your module):" \
  "     go mod edit -replace github.com/aletheia-automotive/aletheia-go=$here/bindings/go" \
  "     go get github.com/aletheia-automotive/aletheia-go/aletheia" \
  "" \
  "   Rust  (in your crate's Cargo.toml):" \
  "     [dependencies]" \
  "     aletheia = { path = \"$here/bindings/rust\" }" \
  "" \
  "----------------------------------------------------------------------" \
  "Full integration guide: docs/development/DISTRIBUTION.md in the source repo."
