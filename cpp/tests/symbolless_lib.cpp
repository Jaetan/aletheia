// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
//
// A shared library carrying none of the kernel's symbols, for the test that a
// refused backend construction closes the library it opened.
extern "C" auto aletheia_test_symbolless() -> int {
    return 0;
}
