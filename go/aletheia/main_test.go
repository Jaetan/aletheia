//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"fmt"
	"os"
	"os/exec"
	"strings"
	"testing"
)

// skipRTSInitEnv, when "1", tells TestMain not to start the GHC runtime, so a
// subprocess can exercise the renderer's uninitialised-runtime path.
const skipRTSInitEnv = "ALETHEIA_TEST_SKIP_RTS_INIT"

// TestMain brings the GHC runtime up once for the whole package. Point-2 made
// the rational renderer a runtime consumer (it no longer self-initialises the
// RTS — see renderer.go), so render-dependent tests — FormatFormula and
// SetProperties (which builds per-property diagnostics) — need an FFIBackend to
// have started the runtime. A throwaway backend's constructor runs hs_init; the
// RTS persists process-wide (hs_exit is never called). Best-effort: if the .so
// is absent, render-dependent tests fail with the renderer's "runtime not
// initialized" error while pure-logic tests still run.
func TestMain(m *testing.M) {
	if os.Getenv(skipRTSInitEnv) != "1" {
		if lib := findFFILibForParityTest(); lib != "" {
			// The constructor runs hs_init, bringing the RTS up for the package.
			if _, err := NewFFIBackend(lib); err != nil {
				fmt.Fprintf(os.Stderr, "TestMain: could not start GHC runtime: %v\n", err)
			}
		}
	}
	os.Exit(m.Run())
}

// TestRenderWithoutRuntimeIsVocal verifies point-2's contract: with the GHC
// runtime uninitialised, the rational renderer returns an error rather than
// panicking or self-initialising. The RTS is process-global and one-shot, so
// the uninitialised state is reproduced in a subprocess where TestMain skips
// the runtime init (the parent process already brought it up).
func TestRenderWithoutRuntimeIsVocal(t *testing.T) {
	if os.Getenv(skipRTSInitEnv) == "1" {
		runRenderWithoutRuntimeChild() // os.Exits; never returns
	}
	lib := findFFILibForParityTest()
	if lib == "" {
		t.Skip("libaletheia-ffi.so not found — run 'cabal run shake -- build' first")
	}
	cmd := exec.Command(os.Args[0], "-test.run=^TestRenderWithoutRuntimeIsVocal$", "-test.v")
	cmd.Env = append(os.Environ(), skipRTSInitEnv+"=1", "ALETHEIA_LIB="+lib)
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("subprocess failed (%v):\n%s", err, out)
	}
	if !strings.Contains(string(out), "RENDER_VOCAL_OK") {
		t.Fatalf("subprocess did not confirm a vocal error:\n%s", out)
	}
}

// runRenderWithoutRuntimeChild runs in the subprocess (runtime init skipped). It
// asserts the renderer is vocal (returns an error), neither panics nor
// self-initialises the runtime, then exits with a code the parent checks.
func runRenderWithoutRuntimeChild() {
	defer func() {
		if r := recover(); r != nil {
			fmt.Printf("FAIL: renderer panicked instead of returning an error: %v\n", r)
			os.Exit(2)
		}
	}()
	if hsInitialized() {
		fmt.Println("FAIL: runtime unexpectedly initialised in subprocess")
		os.Exit(3)
	}
	if _, err := formatRational(Rational{Numerator: 1, Denominator: 2}); err == nil {
		fmt.Println("FAIL: expected an error when the runtime is uninitialised")
		os.Exit(4)
	}
	if hsInitialized() {
		fmt.Println("FAIL: renderer self-initialised the runtime")
		os.Exit(5)
	}
	fmt.Println("RENDER_VOCAL_OK")
	os.Exit(0)
}
