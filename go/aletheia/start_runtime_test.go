//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"bytes"
	"context"
	"errors"
	"fmt"
	"log/slog"
	"os"
	"strings"
	"testing"
)

// StartRuntime starts the kernel's runtime before any client: a program
// starts it, loads checks holding decimals and hands them to a client's
// options; a backend naming no core count asks for the count running; a count
// outside one to the CPUs the process may use is refused, the bound being the
// runtime's own count of them. Each claim is about a process whose runtime
// nothing has started, so each runs in a child of its own, the start
// suppressed. The recording stand-in counts four CPUs on every machine.
func TestStartRuntimeBeforeAnyClient(t *testing.T) {
	if scenario := os.Getenv(loaderScenarioEnv); scenario != "" {
		runStartScenario(scenario) // os.Exits; never returns
	}
	lib := findFFILibrary()
	if lib == "" {
		t.Skip("libaletheia-ffi.so not found; run 'cabal run shake -- build' first")
	}
	recording := standIn(t, lib, "recording_kernel")
	scenarios := map[string][]string{
		"default-checks": {"ALETHEIA_LIB=" + lib},
		"refusals":       {startLibEnv + "=" + lib},
		"bound":          {startLibEnv + "=" + lib},
		"running-count":  {"ALETHEIA_LIB=" + lib},
		"stand-in":       {startLibEnv + "=" + recording},
	}
	for scenario, env := range scenarios {
		t.Run(scenario, func(t *testing.T) {
			// The working directory holds no library, so a consumer that
			// searched for one would find none.
			out := runScenarioChild(t, "TestStartRuntimeBeforeAnyClient", scenario, t.TempDir(), env...)
			if !strings.Contains(out, "START_OK") {
				t.Fatalf("the child did not confirm the scenario:\n%s", out)
			}
		})
	}
}

// startLibEnv names the library a scenario starts the runtime on, which
// ALETHEIA_LIB does not name there.
const startLibEnv = "ALETHEIA_TEST_START_LIB"

// The DBC and the check the default-checks scenario streams: EngineSpeed's
// factor 0.25 decodes raw 800 to 200 rpm, past the 199.5 limit.
const (
	startDBC = `VERSION ""

NS_ :

BS_:

BU_: ECU

BO_ 256 EngineStatus: 8 ECU
 SG_ EngineSpeed : 0|16@1+ (0.25,0) [0|8000] "rpm" ECU
`
	startChecks = `checks:
  - name: Speed limit
    signal: EngineSpeed
    condition: never_exceeds
    value: 199.5
    severity: critical
`
)

// fail ends the child with a numbered exit naming what went wrong.
func fail(code int, format string, args ...any) {
	fmt.Printf("FAIL: "+format+"\n", args...)
	os.Exit(code)
}

// expectText fails the child unless err is exactly an error of kind and text,
// unlocated and carrying no wire code.
func expectText(err error, kind ErrorKind, text string, code int) {
	var e *Error
	switch {
	case !errors.As(err, &e):
		fail(code, "got %v, want an unlocated %v error with no code reading %q", err, kind, text)
	case e.Kind != kind || err.Error() != text || e.Location != "" || e.Key != "" || e.Code != "":
		fail(code, "got %v (kind %v, code %q, location %q, key %q), want an unlocated %v error with no code reading %q",
			err, e.Kind, e.Code, e.Location, e.Key, kind, text)
	}
}

// mismatches counts the rts.cores_mismatch records a log holds, and fails the
// child unless each names the counts.
func mismatches(log *bytes.Buffer, active, requested, code int) int {
	n := strings.Count(log.String(), "rts.cores_mismatch")
	for _, want := range []string{fmt.Sprintf("active_cores=%d", active), fmt.Sprintf("requested_cores=%d", requested)} {
		if n > 0 && !strings.Contains(log.String(), want) {
			fail(code, "the log does not carry %s: %s", want, log.String())
		}
	}
	return n
}

// runStartScenario is the child's body.
func runStartScenario(scenario string) {
	defer func() {
		if r := recover(); r != nil {
			fail(2, "a call panicked instead of answering: %v", r)
		}
	}()
	ctx := context.Background()
	lib := os.Getenv(startLibEnv)
	half := Rational{Numerator: 1, Denominator: 2}
	var log bytes.Buffer
	logger := slog.New(slog.NewTextHandler(&log, nil))
	switch scenario {
	case "default-checks":
		if _, ok := AllocatedBytes(); ok {
			fail(10, "AllocatedBytes answered a count before the runtime started")
		}
		if err := StartRuntimeFromEnv(1, nil); err != nil {
			fail(11, "StartRuntimeFromEnv: %v", err)
		}
		if _, ok := AllocatedBytes(); !ok {
			fail(12, "AllocatedBytes answered no count after the runtime started")
		}
		checks, err := LoadChecksFromYAML(startChecks)
		if err != nil {
			fail(13, "LoadChecksFromYAML: %v", err)
		}
		backend, err := NewFFIBackendFromEnv()
		if err != nil {
			fail(14, "NewFFIBackendFromEnv: %v", err)
		}
		client, err := NewClient(backend, WithDefaultChecks(checks...))
		if err != nil {
			fail(15, "NewClient: %v", err)
		}
		defer client.Close()
		if _, err := client.ParseDBCText(ctx, startDBC); err != nil {
			fail(16, "ParseDBCText: %v", err)
		}
		if err := client.AddChecks(ctx, nil); err != nil {
			fail(17, "AddChecks: %v", err)
		}
		if err := client.StartStream(ctx); err != nil {
			fail(18, "StartStream: %v", err)
		}
		id, _ := NewStandardID(0x100)
		dlc, _ := NewDLC(8)
		resp, err := client.SendFrame(ctx, Timestamp{Microseconds: 1000}, id, dlc,
			FramePayload{0x20, 0x03, 0, 0, 0, 0, 0, 0}, nil, nil)
		if err != nil {
			fail(19, "SendFrame: %v", err)
		}
		if batch, ok := resp.(PropertyBatch); !ok || batch.FirstViolation() == nil {
			fail(20, "the default check holding 199.5 did not fail on 200 rpm: %v", resp)
		}
	case "refusals":
		// Before any start the parser and the renderer name the remedy and
		// open nothing; after one, both read the library the runtime started on.
		_, err := FromDecimal("1.5")
		expectText(err, ErrFFI, "GHC runtime not initialized: call aletheia.StartRuntime or open a client before parsing decimals", 21)
		_, err = formatRational(half)
		expectText(err, ErrFFI, "GHC runtime not initialized: call aletheia.StartRuntime or open a client before rendering", 22)
		// A loader reading a number returns the parser's refusal as it is,
		// unlocated and with no checks, a when-then check reading its time
		// bound first; its own refusal of a document answers on the document.
		const whenThen = "checks:\n  - name: w\n    when:\n      signal: Brake\n      condition: exceeds\n" +
			"      value: 50\n    then:\n      signal: Light\n      condition: equals\n" +
			"      value: 1\n    within_ms: 100\n"
		if err := os.WriteFile("checks.yaml", []byte(startChecks), 0o600); err != nil {
			fail(27, "writing the checks file: %v", err)
		}
		for _, load := range []struct {
			code int
			read func() ([]CheckResult, error)
		}{
			{28, func() ([]CheckResult, error) { return LoadChecksFromYAML(startChecks) }},
			{34, func() ([]CheckResult, error) { return LoadChecksFromYAML(whenThen) }},
			{29, func() ([]CheckResult, error) { return LoadChecksFromYAMLFile("checks.yaml") }},
			{35, func() ([]CheckResult, error) { return LoadChecksFromYAML("checks.yaml") }},
		} {
			checks, err := load.read()
			if checks != nil {
				fail(load.code, "a refused load returned checks: %v", checks)
			}
			expectText(err, ErrFFI, "GHC runtime not initialized: call aletheia.StartRuntime or open a client before parsing decimals", load.code)
		}
		checks, err := LoadChecksFromYAML("not: a checks list\n")
		if checks != nil {
			fail(33, "a refused load returned checks: %v", checks)
		}
		expectText(err, ErrValidation, "YAML document must contain a 'checks' list", 33)
		if hsInitialized() {
			fail(23, "a consumer started the runtime")
		}
		if err := StartRuntime(lib, 1, nil); err != nil {
			fail(24, "StartRuntime: %v", err)
		}
		if got, err := FromDecimal("1.5"); err != nil || got != (Rational{Numerator: 3, Denominator: 2}) {
			fail(25, "FromDecimal after the start answered %v, %v", got, err)
		}
		if got, err := formatRational(half); err != nil || got != "0.5" {
			fail(26, "formatRational after the start answered %q, %v", got, err)
		}
	case "bound":
		// Zero is outside the bound on every machine; the bound's own figure
		// is the machine's, and the stand-in scenario holds the text whole.
		_, backendErr := NewFFIBackend(lib, WithRTSCores(0))
		for i, err := range []error{StartRuntime(lib, 0, nil), backendErr} {
			var e *Error
			if !errors.As(err, &e) || e.Kind != ErrValidation ||
				!strings.HasPrefix(e.Message, "core count 0 is outside 1 to ") ||
				!strings.HasSuffix(e.Message, ", the CPUs this process may use") {
				fail(30+i, "a count of zero answered %v, want its refusal", err)
			}
		}
		if hsInitialized() {
			fail(32, "a refused count started the runtime")
		}
	case "running-count":
		if err := StartRuntimeFromEnv(2, nil); err != nil {
			fail(40, "StartRuntimeFromEnv: %v", err)
		}
		if err := StartRuntimeFromEnv(2, logger); err != nil {
			fail(41, "a second StartRuntimeFromEnv: %v", err)
		}
		if _, err := NewFFIBackendFromEnv(WithFFILogger(logger)); err != nil {
			fail(42, "a backend naming no count: %v", err)
		}
		if n := mismatches(&log, 2, 1, 43); n != 0 {
			fail(44, "the running count asked again was warned: %s", log.String())
		}
		if _, err := NewFFIBackendFromEnv(WithRTSCores(1), WithFFILogger(logger)); err != nil {
			fail(45, "a backend asking one core: %v", err)
		}
		if n := mismatches(&log, 2, 1, 46); n != 1 {
			fail(47, "a backend asking another count was warned %d times: %s", n, log.String())
		}
	case "stand-in":
		for _, past := range []int{0, 5} {
			want := fmt.Sprintf("core count %d is outside 1 to 4, the CPUs this process may use", past)
			expectText(StartRuntime(lib, past, nil), ErrValidation, want, 50)
			_, err := NewFFIBackend(lib, WithRTSCores(past))
			expectText(err, ErrValidation, want, 56)
		}
		if err := StartRuntime(lib, 1, nil); err != nil {
			fail(51, "StartRuntime on the stand-in: %v", err)
		}
		if err := StartRuntime(lib, 4, logger); err != nil {
			fail(52, "StartRuntime asking four of a runtime on one: %v", err)
		}
		if n := mismatches(&log, 1, 4, 53); n != 1 {
			fail(54, "asking four of a runtime on one was warned %d times: %s", n, log.String())
		}
		// The stand-in renders a rational as its two components, so the
		// renderer read the library the runtime started on.
		if got, err := formatRational(half); err != nil || got != "1/2" {
			fail(55, "formatRational answered %q, %v, want the stand-in's 1/2", got, err)
		}
	default:
		fail(1, "unknown scenario %q", scenario)
	}
	fmt.Println("START_OK")
	os.Exit(0)
}
