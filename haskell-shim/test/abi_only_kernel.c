// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
/*
 * A library at the current ABI version that exports that version and nothing
 * else: it passes every loader's version check, so the loader reaches the
 * lookup of its own entries and must refuse at the first one missing. The C++
 * and Go suites compile it into a temporary library.
 */
#include "aletheia.h"

uint32_t aletheia_abi_version(void) {
    return ALETHEIA_ABI_VERSION;
}
