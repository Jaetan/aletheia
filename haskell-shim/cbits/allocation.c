// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
/*
 * The bytes the GHC runtime has allocated since it started. The runtime adds
 * an allocation area to its count only when it collects that area, so a
 * collection runs first and the count covers every allocation made before
 * the call.
 */
#include <Rts.h>

#include "aletheia.h"

uint64_t aletheia_allocated_bytes(void) {
    RTSStats stats;
    performGC();
    getRTSStats(&stats);
    return stats.allocated_bytes;
}
