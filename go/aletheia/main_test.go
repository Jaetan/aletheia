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

// skipRTSInitEnv, set to one, tells the entry below to leave the GHC runtime
// down, which is how a subprocess reaches the paths that need it and have it
// not.
const skipRTSInitEnv = "ALETHEIA_TEST_SKIP_RTS_INIT"

// TestMain starts the GHC runtime once for the package. The rational renderer
// and the decimal parser read it and do not start it, so the tests that render
// need it already up; opening one backend does that, and the runtime stays up
// for the process, there being no way to take it down. Without the library the
// tests that render fail with the renderer's own refusal, and the rest run.
func TestMain(m *testing.M) {
	if os.Getenv(skipRTSInitEnv) != "1" {
		if lib := findFFILibrary(); lib != "" {
			// The constructor runs hs_init, bringing the RTS up for the package.
			if _, err := NewFFIBackend(lib); err != nil {
				fmt.Fprintf(os.Stderr, "TestMain: could not start GHC runtime: %v\n", err)
			}
		}
	}
	os.Exit(m.Run())
}

// With the runtime down, the two consumers that need it refuse rather than
// panicking, and neither starts it behind the caller's back. The runtime is
// process-wide and starts once, so the state under test only exists in a fresh
// process: this one re-runs itself with the start suppressed.
func TestRenderWithoutRuntimeIsVocal(t *testing.T) {
	if os.Getenv(skipRTSInitEnv) == "1" {
		runRenderWithoutRuntimeChild() // os.Exits; never returns
	}
	lib := findFFILibrary()
	if lib == "" {
		t.Skip("libaletheia-ffi.so not found; run 'cabal run shake -- build' first")
	}
	cmd := exec.Command(os.Args[0], "-test.run=^TestRenderWithoutRuntimeIsVocal$", "-test.v")
	// The two variables are removed before they are set, so the child sees one
	// of each: a build that exports the library path would otherwise leave two,
	// and which one the child reads is the environment's business.
	env := make([]string, 0, len(os.Environ())+2)
	for _, e := range os.Environ() {
		if strings.HasPrefix(e, "ALETHEIA_LIB=") || strings.HasPrefix(e, skipRTSInitEnv+"=") {
			continue
		}
		env = append(env, e)
	}
	cmd.Env = append(env, skipRTSInitEnv+"=1", "ALETHEIA_LIB="+lib)
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("subprocess failed (%v):\n%s", err, out)
	}
	if !strings.Contains(string(out), "RENDER_VOCAL_OK") {
		t.Fatalf("subprocess did not confirm a vocal error:\n%s", out)
	}
}

// runRenderWithoutRuntimeChild is the body of the subprocess, where the
// runtime was never started. Each consumer must refuse with a library error
// and leave the runtime down; a panic, a success, another kind of error or a
// runtime that came up behind the call each exit with a code of their own, so
// the parent's output names which one failed.
func runRenderWithoutRuntimeChild() {
	defer func() {
		if r := recover(); r != nil {
			fmt.Printf("FAIL: a consumer panicked instead of refusing: %v\n", r)
			os.Exit(2)
		}
	}()
	if hsInitialized() {
		fmt.Println("FAIL: the runtime is up in a process that was told not to start it")
		os.Exit(3)
	}
	consumers := []struct {
		name string
		call func() error
		code int
	}{
		{"the rational renderer", func() error {
			_, err := formatRational(Rational{Numerator: 1, Denominator: 2})
			return err
		}, 4},
		{"the decimal parser", func() error {
			_, err := FromDecimal("0.1")
			return err
		}, 6},
	}
	for _, consumer := range consumers {
		err := consumer.call()
		var ffiErr *Error
		if err == nil || !errors.As(err, &ffiErr) || ffiErr.Kind != ErrFFI {
			fmt.Printf("FAIL: %s answered %v, want a library error\n", consumer.name, err)
			os.Exit(consumer.code)
		}
		if hsInitialized() {
			fmt.Printf("FAIL: %s started the runtime\n", consumer.name)
			os.Exit(consumer.code + 1)
		}
	}
	fmt.Println("RENDER_VOCAL_OK")
	os.Exit(0)
}
