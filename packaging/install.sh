#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2025 Nicolas Pelletier
# SPDX-License-Identifier: BSD-2-Clause
#
# Aletheia installer (bash / zsh).  Prints how to wire the bundled library and
# language bindings into your shell and toolchain.  It does NOT edit your
# ~/.bashrc, ~/.zshrc, or config.fish — you stay in control; it prints the
# exact line to add.
set -euo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]:-$0}")" >/dev/null 2>&1 && pwd)"
lib="${here}/lib/libaletheia-ffi.so"

if [[ ! -f "${lib}" ]]; then
    printf 'error: %s not found — run this from the unpacked aletheia bundle.\n' "${lib}" >&2
    exit 1
fi

# Defense-in-depth: the Python loader rejects a group/world-writable .so.
# `cp`/`tar` preserve owner-write-only permissions (0644/0755), so this is
# normally a no-op; it hardens against an unpack that widened the mode.
chmod go-w "${here}"/lib/*.so* 2>/dev/null || true

cat <<EOF
Aletheia is unpacked at:
  ${here}

----------------------------------------------------------------------
1. Make the library discoverable (sets ALETHEIA_LIB).  Add the matching
   line to your shell startup file, or run it now for this shell only:

     bash / zsh   (~/.bashrc or ~/.zshrc):
       source "${here}/env.sh"

     fish         (~/.config/fish/config.fish):
       source "${here}/env.fish"

----------------------------------------------------------------------
2. Use Aletheia from your language (each reads ALETHEIA_LIB at runtime):

   Python  (requires Python 3.14+; no third-party runtime dependencies):
     # In a virtual environment you have created and activated:
     pip install "${here}/bindings/python"
     # Or, with no venv (works on an externally-managed / PEP 668 Python),
     # install into an isolated directory and put it on PYTHONPATH:
     pip install --target "${HOME}/.local/lib/aletheia" "${here}/bindings/python"
     export PYTHONPATH="${HOME}/.local/lib/aletheia"
     python -c 'import aletheia; from aletheia import FFIBackend; FFIBackend()'

   C++  (CMake; fetches nlohmann/json + yaml-cpp + OpenXLSX at configure time):
     # in your project's CMakeLists.txt:
     add_subdirectory("${here}/bindings/cpp" aletheia-cpp)
     target_link_libraries(your_app PRIVATE aletheia::aletheia-cpp)

   Go  (in your module):
     go mod edit -replace "github.com/aletheia-automotive/aletheia-go=${here}/bindings/go"
     go get github.com/aletheia-automotive/aletheia-go/aletheia

   Rust  (in your crate's Cargo.toml):
     [dependencies]
     aletheia = { path = "${here}/bindings/rust" }

----------------------------------------------------------------------
Full integration guide: docs/development/DISTRIBUTION.md in the source repo.
EOF
