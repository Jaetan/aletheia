// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// A shared library carrying none of the kernel's symbols, for the tests that
// a backend, the renderer and the decimal parser each refuse a library that
// opens but resolves nothing, naming the symbol they asked for.
int aletheia_test_symbolless(void) {
    return 0;
}
