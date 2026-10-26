//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package excel

import (
	"errors"
	"fmt"
	"os"
	"os/exec"
	"strings"
	"testing"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
)

// The when-then workbook's and the DBC workbook's paths in a child of
// TestLoadersBeforeAnyStart, beside runtimeDownEnv's checks workbook.
const (
	runtimeDownWhenThenEnv = "ALETHEIA_TEST_EXCEL_RUNTIME_DOWN_WHEN_THEN"
	runtimeDownDBCEnv      = "ALETHEIA_TEST_EXCEL_RUNTIME_DOWN_DBC"
)

// A load reading a number before any start returns the decimal parser's
// refusal as it is, unlocated and with no result, and starts nothing; a
// loader's own refusal of a workbook that does not exist answers on the path.
// The runtime starts once per process and TestMain starts it, so the claim
// runs in a child whose TestMain does not.
func TestLoadersBeforeAnyStart(t *testing.T) {
	if checks := os.Getenv(runtimeDownEnv); checks != "" {
		loadBeforeAnyStart(checks, os.Getenv(runtimeDownWhenThenEnv), os.Getenv(runtimeDownDBCEnv)) // os.Exits
	}
	checks := makeChecksWorkbook(t, [][]any{{nil, "Speed", "never_exceeds", 220, nil, nil, nil, nil}})
	whenThen := makeWhenThenWorkbook(t, [][]any{
		{nil, "BrakePedal", "exceeds", 50, "BrakeLight", "equals", 1, nil, nil, 100, nil},
	})
	dbc := makeDBCWorkbook(t, [][]any{
		{256, "EngineData", "FALSE", 8, "RPM", 0, 16, "little_endian", "FALSE", 0.25, 0, 0, 16383.75, "rpm"},
	})
	exe, err := os.Executable()
	if err != nil {
		t.Fatalf("the test binary's own path: %v", err)
	}
	cmd := exec.Command(exe, "-test.run=^TestLoadersBeforeAnyStart$", "-test.v")
	cmd.Dir = t.TempDir()
	env := make([]string, 0, len(os.Environ())+3)
	for _, e := range os.Environ() {
		if !strings.HasPrefix(e, "ALETHEIA_LIB=") {
			env = append(env, e)
		}
	}
	cmd.Env = append(env, runtimeDownEnv+"="+checks, runtimeDownWhenThenEnv+"="+whenThen, runtimeDownDBCEnv+"="+dbc)
	out, err := cmd.CombinedOutput()
	if err != nil || !strings.Contains(string(out), "RUNTIME_DOWN_OK") {
		t.Fatalf("the child did not confirm the refusals (%v):\n%s", err, out)
	}
}

// loadBeforeAnyStart is the child's body: it exits with a numbered status
// naming the first load that answered otherwise.
func loadBeforeAnyStart(checks, whenThen, dbc string) {
	const refused = "GHC runtime not initialized: call aletheia.StartRuntime or open a client before parsing decimals"
	fail := func(code int, format string, args ...any) {
		fmt.Printf("FAIL: "+format+"\n", args...)
		os.Exit(code)
	}
	expect := func(err error, kind aletheia.ErrorKind, text string, code int) {
		var e *aletheia.Error
		switch {
		case !errors.As(err, &e):
			fail(code, "got %v, want an unlocated %v error with no code reading %q", err, kind, text)
		case e.Kind != kind || err.Error() != text || e.Location != "" || e.Key != "" || e.Code != "":
			fail(code, "got %v (kind %v, code %q, location %q, key %q), want an unlocated %v error with no code reading %q",
				err, e.Kind, e.Code, e.Location, e.Key, kind, text)
		}
	}
	for _, load := range []struct {
		code int
		path string
	}{{10, checks}, {13, whenThen}} {
		loaded, err := LoadChecks(load.path)
		if loaded != nil {
			fail(load.code, "a refused load returned checks: %v", loaded)
		}
		expect(err, aletheia.ErrFFI, refused, load.code)
	}
	definition, err := LoadDbc(dbc)
	if definition != nil {
		fail(11, "a refused load returned a DBC: %v", definition)
	}
	expect(err, aletheia.ErrFFI, refused, 11)
	missing, err := LoadChecks("does-not-exist.xlsx")
	if missing != nil {
		fail(12, "a refused load returned checks: %v", missing)
	}
	expect(err, aletheia.ErrValidation, "excel file not found: does-not-exist.xlsx", 12)
	if _, started := aletheia.AllocatedBytes(); started {
		fail(14, "a loader started the runtime")
	}
	fmt.Println("RUNTIME_DOWN_OK")
	os.Exit(0)
}
