//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Runtime GHC RTS heap-cap containment — Go behavioural test.
//
// CONTAINMENT-BY-ABORT: the heap cap is NOT a recoverable error.  When it fires
// the process TERMINATES (a GHC HeapExhausted abort of the foreign-export
// wrapper) so the HOST survives.  This test proves both directions out-of-
// process (the abort is process-terminating and the GHC RTS is one-shot per
// process, so it cannot be exercised in the parent):
//
//	positive — the correct path (hs_init_with_rtsopts + -M3G) boots and parses;
//	negative — a tight ALETHEIA_RTS_OPTS=-M12M cap over a large DBC aborts.
//
// The child is this same test binary re-exec'd with a sentinel env var; when it
// is set the test body runs the workload and exits instead of running the
// assertions.

package aletheia

import (
	"context"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"testing"
)

const (
	rtsChildEnv  = "ALETHEIA_RTS_WORKLOAD_CHILD"
	rtsCountEnv  = "ALETHEIA_RTS_WORKLOAD_N"
	rtsSentinel  = "ALETHEIA_RTS_OK"
	rtsChildTest = "^TestRTSHeapCapContainment$"
)

// rtsWorkloadDBC builds a VALID DBC of n messages; a large n yields a parse
// tree well past a tight -M cap (so the cap fires mid-parse, aborting the
// process), a small n fits any cap and parses cleanly.
func rtsWorkloadDBC(n int) string {
	var b strings.Builder
	b.WriteString("VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\n")
	for i := 0; i < n; i++ {
		fmt.Fprintf(&b, "BO_ %d Msg%d: 8 ECU\n", 256+i, i)
		fmt.Fprintf(&b, " SG_ Sig%d : 0|16@1+ (0.25,0) [0|8000] \"u\" ECU\n\n", i)
	}
	return b.String()
}

// runRTSWorkloadChild runs in the re-exec'd child: boot the real FFI client and
// parse the workload DBC, then print the sentinel.  Under a tight cap the parse
// aborts the process before the sentinel is reached.  Never returns.
func runRTSWorkloadChild() {
	backend, err := NewFFIBackend(os.Getenv("ALETHEIA_LIB"))
	if err != nil {
		fmt.Fprintln(os.Stderr, "child backend:", err)
		os.Exit(2)
	}
	client, err := NewClient(backend)
	if err != nil {
		fmt.Fprintln(os.Stderr, "child client:", err)
		os.Exit(2)
	}
	n, _ := strconv.Atoi(os.Getenv(rtsCountEnv))
	if _, err := client.ParseDBCText(context.Background(), rtsWorkloadDBC(n)); err != nil {
		fmt.Fprintln(os.Stderr, "child parse:", err)
		os.Exit(3)
	}
	fmt.Println(rtsSentinel)
	os.Exit(0)
}

func TestRTSHeapCapContainment(t *testing.T) {
	if os.Getenv(rtsChildEnv) == "1" {
		runRTSWorkloadChild()
		return // unreachable: runRTSWorkloadChild always exits
	}

	lib := findFFILibForParityTest()
	if lib == "" {
		t.Skip("libaletheia-ffi.so not found — run 'cabal run shake -- build' first")
	}
	absLib, err := filepath.Abs(lib)
	if err != nil {
		t.Fatalf("abs lib path: %v", err)
	}

	run := func(n int, rtsOpts string) (string, int) {
		t.Helper()
		cmd := exec.Command(os.Args[0], "-test.run="+rtsChildTest)
		cmd.Env = append(os.Environ(),
			rtsChildEnv+"=1",
			"ALETHEIA_LIB="+absLib,
			rtsCountEnv+"="+strconv.Itoa(n),
		)
		if rtsOpts != "" {
			cmd.Env = append(cmd.Env, "ALETHEIA_RTS_OPTS="+rtsOpts)
		} else {
			// Ensure no ambient ALETHEIA_RTS_OPTS leaks into the positive path.
			cmd.Env = append(cmd.Env, "ALETHEIA_RTS_OPTS=")
		}
		out, _ := cmd.CombinedOutput()
		return string(out), cmd.ProcessState.ExitCode()
	}

	t.Run("default cap boots and processes", func(t *testing.T) {
		out, code := run(5, "")
		if code != 0 {
			t.Fatalf("expected clean exit, got %d; output:\n%s", code, out)
		}
		if !strings.Contains(out, rtsSentinel) {
			t.Fatalf("missing success sentinel; output:\n%s", out)
		}
	})

	t.Run("tight cap aborts the process", func(t *testing.T) {
		out, code := run(1000, "-M12M")
		if code == 0 {
			t.Fatalf("expected non-zero abort under -M12M, got 0; output:\n%s", out)
		}
		if strings.Contains(out, rtsSentinel) {
			t.Fatalf("success sentinel printed under a tight cap; output:\n%s", out)
		}
		// Exit 3 is the workload's own parse-error path; a valid DBC never takes
		// it, so a non-zero, non-3 exit is the GHC heap abort (containment).
		if code == 3 {
			t.Fatalf("workload hit a parse error, not a heap abort; output:\n%s", out)
		}
	})
}
