// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// The client's factory, linked from the installed package, refuses a library
// that does not exist; the refusal coming back is the pass.
#include <aletheia/aletheia.hpp>

int main() {
    auto const backend = aletheia::make_ffi_backend("/nonexistent/libaletheia-ffi.so");
    return backend.has_value() ? 1 : 0;
}
