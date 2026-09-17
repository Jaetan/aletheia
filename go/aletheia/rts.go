// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

// The arguments the GHC runtime is started with. The values are
// docs/RESOURCE_BUDGETS.yaml's, mirrored here; tools/check_rts_runtime.py and
// rts_params_parity_test.go hold the mirror to it.
//
// The heap cap contains rather than reports. Without it the runtime has no
// limit, so an allocation that runs away takes the host's memory and the
// kernel of the operating system kills whatever it chooses. With it, the same
// allocation trips the runtime's own check and the process ends: there is no
// error to catch and no partial answer, and the host lives. The cap is set for
// containment with room to spare, the heaviest working set observed being
// about 1.5 gibibytes, and is not a budget anyone tuned.

import (
	"fmt"
	"os"
	"strings"
)

const (
	// rtsHeapCapFlag is the heap cap every process gets.
	rtsHeapCapFlag = "-M3G"
	// rtsDefaultCores is what one bus needs; a core count is passed to the
	// runtime only when a caller asks for more than this.
	rtsDefaultCores = 1
	// rtsInitSymbol starts the runtime. The plainer entry point refuses the
	// heap cap, the library being linked to allow only the safe options, and
	// aborts saying so; this one takes every flag. Both have the same C
	// signature, so which is called is only this string.
	rtsInitSymbol = "hs_init_with_rtsopts"
	// rtsOverrideEnv names the variable whose flags are appended last, so a
	// cap given there replaces the one above: the runtime takes the last of a
	// repeated flag.
	rtsOverrideEnv = "ALETHEIA_RTS_OPTS"
)

// rtsOverrideFlags are the flags the environment adds, none when it sets
// nothing, with which one process can tighten or extend what the runtime gets.
func rtsOverrideFlags() []string {
	return strings.Fields(os.Getenv(rtsOverrideEnv))
}

// rtsInitArgv is the argument vector the runtime is started with, in the
// order the budgets document fixes: the program name, the cap, a core count
// when one was asked for, whatever the environment adds, and the closing
// marker. It touches nothing outside itself, so a test can read it directly.
// The cap is in every vector, whatever the core count.
func rtsInitArgv(cores int) []string {
	argv := []string{"aletheia", "+RTS", rtsHeapCapFlag}
	if cores > rtsDefaultCores {
		argv = append(argv, fmt.Sprintf("-N%d", cores))
	}
	argv = append(argv, rtsOverrideFlags()...)
	return append(argv, "-RTS")
}
