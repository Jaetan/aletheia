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
			if got := rtsInitArgv(tc.cores, tc.override); !slices.Equal(got, tc.want) {
				t.Errorf("got %v, want %v", got, tc.want)
			}
		})
	}
}

// The words are split on the six ASCII whitespace bytes, space, TAB, LF, CR,
// VT and FF, as the C++ and Python bindings split them: each of the six
// separates two words, and every other byte stays in its word, a Unicode
// space, an ASCII control byte and a byte that is not UTF-8 alike.
func TestRTSInitArgvSplitsOnASCIIWhitespace(t *testing.T) {
	cases := map[string]struct {
		override string
		words    []string
	}{
		"a space":                           {"-a -b", []string{"-a", "-b"}},
		"a TAB":                             {"-a\t-b", []string{"-a", "-b"}},
		"an LF":                             {"-a\n-b", []string{"-a", "-b"}},
		"a CR":                              {"-a\r-b", []string{"-a", "-b"}},
		"a VT":                              {"-a\v-b", []string{"-a", "-b"}},
		"an FF":                             {"-a\f-b", []string{"-a", "-b"}},
		"NBSP, NEL and FS stay in the word": {"-a\xc2\xa0-b\xc2\x85-c\x1c-d", []string{"-a\xc2\xa0-b\xc2\x85-c\x1c-d"}},
		"a byte that is not UTF-8 stays in the word": {"-a\xff-b", []string{"-a\xff-b"}},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			want := slices.Concat([]string{"aletheia", "+RTS", rtsHeapCapFlag}, tc.words, []string{"-RTS"})
			if got := rtsInitArgv(rtsDefaultCores, tc.override); !slices.Equal(got, want) {
				t.Errorf("got %q, want %q", got, want)
			}
		})
	}
}
