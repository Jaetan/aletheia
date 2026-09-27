// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
/*
 * The ABI version export, in C rather than Haskell so that a binding can call
 * it before it starts the GHC runtime: a library whose version is not the
 * binding's is refused before anything in it runs.
 */
#include "aletheia.h"

uint32_t aletheia_abi_version(void) {
    return ALETHEIA_ABI_VERSION;
}
