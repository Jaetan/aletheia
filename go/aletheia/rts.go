// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

// Runtime GHC RTS parameters — SSOT: docs/RESOURCE_BUDGETS.yaml (runtime
// block); mirrored here verbatim.  Parity with the SSOT is enforced by
// tools/check_rts_runtime.py (a run_ci gate) and rts_params_parity_test.go.
//
// CONTAINMENT-BY-ABORT contract: the heap cap does NOT yield a recoverable
// error.  The loaded kernel's GHC RTS has no heap limit by default, so a
// runaway allocation exhausts host memory and the OOM killer takes the whole
// machine down.  With the cap in place the same runaway trips GHC's
// heap-overflow check and the foreign-export wrapper aborts the PROCESS
// (`aletheia: aletheia_process: Return code (4) not ok`).  There is no
// catchable error and no partial result — the host survives, the process does
// not.  This is a containment bound with measured headroom (heaviest kernel
// working set observed ~1.5 GiB), never a tuned working-set budget.

import (
	"fmt"
	"os"
	"strings"
)

const (
	// rtsHeapCapFlag is the default -M heap cap emitted into the RTS argv.
	rtsHeapCapFlag = "-M3G"
	// rtsDefaultCores is the GHC capability count for single-bus monitoring;
	// a -N flag is emitted only when a caller requests more.
	rtsDefaultCores = 1
	// rtsInitSymbol is the GHC entry point that starts the RTS.  Plain hs_init
	// cannot carry the -M cap under the .so's link-time RtsOptsSafeOnly (it
	// aborts at init with "Most RTS options are disabled");
	// hs_init_with_rtsopts honours the full flag set.  Same C signature
	// (void(int*, char***)), so the switch is a pure string change.
	rtsInitSymbol = "hs_init_with_rtsopts"
	// rtsOverrideEnv names the environment variable whose whitespace-split
	// flags are appended after the cap (and after an optional -N), so a caller
	// -M in it wins (the RTS honours the last occurrence).
	rtsOverrideEnv = "ALETHEIA_RTS_OPTS"
)

// rtsOverrideFlags returns the whitespace-split flags from ALETHEIA_RTS_OPTS
// (empty when unset), appended after the mirrored cap so a caller can tighten
// or extend a single process's RTS options.
func rtsOverrideFlags() []string {
	return strings.Fields(os.Getenv(rtsOverrideEnv))
}

// rtsInitArgv assembles the argv passed to hs_init_with_rtsopts, per the SSOT
// argv_order: {progname, +RTS, heap_cap, -N<k> iff k>1, override flags, -RTS}.
// Pure (no cgo), so it is unit-testable and the parity test can drive it
// directly.  The cap is ALWAYS present, so the host is protected regardless of
// the requested core count.
func rtsInitArgv(cores int) []string {
	argv := []string{"aletheia", "+RTS", rtsHeapCapFlag}
	if cores > rtsDefaultCores {
		argv = append(argv, fmt.Sprintf("-N%d", cores))
	}
	argv = append(argv, rtsOverrideFlags()...)
	return append(argv, "-RTS")
}
