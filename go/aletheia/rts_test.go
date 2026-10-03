// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// The argument vector the runtime is started with is built in the order
// docs/RESOURCE_BUDGETS.yaml fixes. The test sits inside the package so that it
// reads the constants themselves, which are unexported here as they are in
// every other binding. Nothing here loads the library.
package aletheia

import (
	"slices"
	"testing"
)

// The vector carries the cap whatever the core count, names a core count only
// when one was asked for, and puts the environment's flags last, where a cap
// among them replaces the one before it.
func TestRTSInitArgv(t *testing.T) {
	cases := map[string]struct {
		cores    int
		override string
		want     []string
	}{
		"one core": {
			1, "", []string{"aletheia", "+RTS", rtsHeapCapFlag, "-RTS"},
		},
		"four cores": {
			4, "", []string{"aletheia", "+RTS", rtsHeapCapFlag, "-N4", "-RTS"},
		},
		"the environment adds flags": {
			1, "  -M12M   -hT ", []string{"aletheia", "+RTS", rtsHeapCapFlag, "-M12M", "-hT", "-RTS"},
		},
		"and adds them beside a core count": {
			2, "-hT", []string{"aletheia", "+RTS", rtsHeapCapFlag, "-N2", "-hT", "-RTS"},
		},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			t.Setenv(rtsOverrideEnv, tc.override)
			if got := rtsInitArgv(tc.cores); !slices.Equal(got, tc.want) {
				t.Errorf("got %v, want %v", got, tc.want)
			}
		})
	}
}
