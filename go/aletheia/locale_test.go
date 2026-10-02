//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"errors"
	"fmt"
	"os"
	"os/exec"
	"strings"
	"testing"
)

// localeChildEnv, set to one, makes TestKernelStringsUnderTheCLocale run its
// checks instead of starting a process that does.
const localeChildEnv = "ALETHEIA_TEST_LOCALE_CHILD"

// localeSentinel is the child's last line, printed once every check passed.
const localeSentinel = "ALETHEIA_LOCALE_OK"

// localeDBCText is one message whose signal has the unit "°C": the text
// reaches the kernel as UTF-8 and the unit comes back in its response.
const localeDBCText = "VERSION \"1.0\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\n" +
	"BO_ 256 M: 8 ECU\n SG_ T : 0|16@1+ (1,0) [0|65535] \"°C\" Vector__XXX\n"

// The kernel reads and writes its strings as UTF-8 whatever the locale of the
// process that loaded it. The GHC runtime reads the locale once, when it
// starts, so the test re-runs itself with LC_ALL=C, where non-ASCII text must
// still cross the kernel intact both ways.
func TestKernelStringsUnderTheCLocale(t *testing.T) {
	if os.Getenv(localeChildEnv) == "1" {
		runLocaleChecks(t)
		return
	}
	if findFFILibrary() == "" {
		t.Skip("libaletheia-ffi.so not found; run 'cabal run shake -- build' first")
	}
	cmd := exec.Command(os.Args[0], "-test.run=^TestKernelStringsUnderTheCLocale$", "-test.v")
	env := make([]string, 0, len(os.Environ())+2)
	for _, e := range os.Environ() {
		if strings.HasPrefix(e, "LC_ALL=") || strings.HasPrefix(e, localeChildEnv+"=") {
			continue
		}
		env = append(env, e)
	}
	cmd.Env = append(env, "LC_ALL=C", localeChildEnv+"=1")
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("child under LC_ALL=C failed (%v):\n%s", err, out)
	}
	if !strings.Contains(string(out), localeSentinel) {
		t.Fatalf("child under LC_ALL=C did not reach its sentinel:\n%s", out)
	}
}

// runLocaleChecks is the child's body: a refused non-ASCII literal, and a
// non-ASCII unit that comes back whole.
func runLocaleChecks(t *testing.T) {
	if got := os.Getenv("LC_ALL"); got != "C" {
		t.Fatalf("the child runs under LC_ALL=%q, not C, so it proves nothing", got)
	}
	_, err := FromDecimal("1.5€")
	var aErr *Error
	if !errors.As(err, &aErr) || aErr.Kind != ErrValidation {
		t.Errorf("FromDecimal accepted 1.5 and a euro sign, or refused it as %v", err)
	}
	parsed, err := newFFIClient(t).ParseDBCText(t.Context(), localeDBCText)
	if err != nil {
		t.Fatalf("ParseDBCText: %v", err)
	}
	if unit := parsed.DBC.Messages[0].Signals[0].Unit; unit != "°C" {
		t.Errorf("the unit came back as %q", unit)
	}
	if !t.Failed() {
		fmt.Println(localeSentinel)
	}
}
