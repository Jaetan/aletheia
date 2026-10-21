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
// reaches the kernel as UTF-8, and the kernel refuses the degree sign, outside
// the DBC character set, at its line and column.
const localeDBCText = "VERSION \"1.0\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\n" +
	"BO_ 256 M: 8 ECU\n SG_ T : 0|16@1+ (1,0) [0|65535] \"°C\" Vector__XXX\n"

// localeRawCommand is a message whose type is the two characters "°C": the
// kernel echoes them whole in its refusal, so non-ASCII text crosses the
// kernel both ways.
const localeRawCommand = `{"type": "°C"}`

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

// runLocaleChecks is the child's body: a refused non-ASCII literal, a
// non-ASCII unit refused at its position, and a non-ASCII message type echoed
// whole.
func runLocaleChecks(t *testing.T) {
	if got := os.Getenv("LC_ALL"); got != "C" {
		t.Fatalf("the child runs under LC_ALL=%q, not C, so it proves nothing", got)
	}
	_, err := FromDecimal("1.5€")
	var aErr *Error
	if !errors.As(err, &aErr) || aErr.Kind != ErrValidation || aErr.Code != CodeTextTrailingInput {
		t.Errorf("FromDecimal accepted 1.5 and a euro sign, or refused it as %v", err)
	}
	_, err = newFFIClient(t).ParseDBCText(t.Context(), localeDBCText)
	if !errors.As(err, &aErr) || aErr.Code != CodeDBCInvalidCharacter ||
		!strings.Contains(aErr.Message, "line 10, column 35 (code point 176)") {
		t.Errorf("ParseDBCText answered the degree sign with %v", err)
	}
	backend, err := NewFFIBackend(findFFILibrary())
	if err != nil {
		t.Fatalf("NewFFIBackend: %v", err)
	}
	state, err := backend.Init()
	if err != nil {
		t.Fatalf("Init: %v", err)
	}
	defer backend.Close(state)
	reply, err := backend.Process(state, localeRawCommand)
	if err != nil || !strings.Contains(reply, "unknown message type '°C'") {
		t.Errorf("the degree sign came back as %q (%v)", reply, err)
	}
	if !t.Failed() {
		fmt.Println(localeSentinel)
	}
}
