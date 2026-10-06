// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
/*
 * A library at an ABI version no binding was written against, and nothing
 * else: every binding's loader reads the version before any other symbol, so
 * this is all a loader sees before it must refuse. The build makes it beside
 * the library, where the bindings' tests load it.
 */
#include "aletheia.h"

uint32_t aletheia_abi_version(void) {
    return ALETHEIA_ABI_VERSION + 1;
}
