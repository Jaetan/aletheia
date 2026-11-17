// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause
/*
 * The bytes the GHC runtime has allocated since it started. The runtime adds
 * an allocation area to its count when it collects the area, and a block of
 * pinned objects when it retires the block for a new one, so the bytes in a
 * capability's current pinned block are in no count. The call retires each
 * capability's current pinned block, then collects, so the count covers every
 * allocation made before the call, less the objects the call places to retire
 * the blocks.
 */
#include <Rts.h>
#include <pthread.h>

#include "aletheia.h"

/*
 * A retiring object: a byte array of 400 words, under the 8/10 of a block from
 * which the runtime makes an object a large one, so it goes in a pinned block,
 * and over half a block, so two never share one. Of the pair a call places on
 * a capability, the second does not fit beside the first, so every block
 * holding an earlier object is retired, and the second stays unbooked in the
 * capability's new current block until the next call retires it.
 */
enum { RETIRING_WORDS = 400 };

// Two calls at once would each book objects the other has not yet counted.
static pthread_mutex_t reading = PTHREAD_MUTEX_INITIALIZER;
static uint64_t retiring_placed;
// The most capabilities a call has retired: one unbooked object each.
static uint32_t capabilities_retired;

static void place_retiring_object(Capability *cap) {
    StgArrBytes *const array = (StgArrBytes *)allocatePinned(cap, RETIRING_WORDS, sizeof(W_), 0);
    SET_ARR_HDR(array, &stg_ARR_WORDS_info, CCS_SYSTEM,
                (RETIRING_WORDS - sizeofW(StgArrBytes)) * sizeof(W_));
}

uint64_t aletheia_allocated_bytes() {
    pthread_mutex_lock(&reading);
    uint32_t const capabilities = enabled_capabilities;
    for (uint32_t i = 0; i < capabilities; i++) {
        rts_setInCallCapability((int)i, 0);
        Capability *const cap = rts_lock();
        place_retiring_object(cap);
        place_retiring_object(cap);
        rts_unlock(cap);
    }
    rts_setInCallCapability(-1, 0);
    retiring_placed += 2 * (uint64_t)capabilities;
    if (capabilities > capabilities_retired) {
        capabilities_retired = capabilities;
    }
    RTSStats stats;
    performGC();
    getRTSStats(&stats);
    uint64_t const own = (retiring_placed - capabilities_retired) * RETIRING_WORDS * sizeof(W_);
    pthread_mutex_unlock(&reading);
    return stats.allocated_bytes - own;
}
