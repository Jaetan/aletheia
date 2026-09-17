//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// The heap cap contains by ending the process, so both directions are proved
// in a child: the runtime starts once per process and the abort ends it, so
// neither can be reached twice in the parent. The child is this same binary
// run again with a variable set, which makes the test body do the work and
// exit rather than assert.
//
// The cap the binding sets boots and parses a small definition; a cap tightened
// through the environment, over a definition large enough to cross it, ends the
// child with the runtime's own message rather than returning an error.

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

	// rtsSetupFailed is the child's exit when the library or the client would
	// not open, and rtsParseFailed when the definition was refused. Neither is
	// the abort under test, so both are named rather than counted as one.
	rtsSetupFailed = 2
	rtsParseFailed = 3

	// rtsAbortMessage is what the runtime prints as it ends the process on a
	// heap it cannot grow. Without it a child that died for another reason
	// would read as containment.
	rtsAbortMessage = "Return code (4) not ok"
)

// rtsWorkloadDBC is a valid definition of n messages. A large n builds a parse
// tree past a tight cap, so the cap fires while parsing; a small one fits under
// any cap and parses.
func rtsWorkloadDBC(n int) string {
	var b strings.Builder
	b.WriteString("VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\n")
	for i := 0; i < n; i++ {
		fmt.Fprintf(&b, "BO_ %d Msg%d: 8 ECU\n", 256+i, i)
		fmt.Fprintf(&b, " SG_ Sig%d : 0|16@1+ (0.25,0) [0|8000] \"u\" ECU\n\n", i)
	}
	return b.String()
}

// runRTSWorkloadChild is the child: open the library, parse the definition,
// print the sentinel. Under a tight cap the parse never returns, so the
// sentinel is never printed. It always exits.
func runRTSWorkloadChild() {
	backend, err := NewFFIBackend(os.Getenv("ALETHEIA_LIB"))
	if err != nil {
		fmt.Fprintln(os.Stderr, "child backend:", err)
		os.Exit(rtsSetupFailed)
	}
	client, err := NewClient(backend)
	if err != nil {
		fmt.Fprintln(os.Stderr, "child client:", err)
		os.Exit(rtsSetupFailed)
	}
	n, _ := strconv.Atoi(os.Getenv(rtsCountEnv))
	if _, err := client.ParseDBCText(context.Background(), rtsWorkloadDBC(n)); err != nil {
		fmt.Fprintln(os.Stderr, "child parse:", err)
		os.Exit(rtsParseFailed)
	}
	fmt.Println(rtsSentinel)
	os.Exit(0)
}

func TestRTSHeapCapContainment(t *testing.T) {
	if os.Getenv(rtsChildEnv) == "1" {
		runRTSWorkloadChild()
		return // unreachable: runRTSWorkloadChild always exits
	}

	lib := findFFILibrary()
	if lib == "" {
		t.Skip("libaletheia-ffi.so not found; run 'cabal run shake -- build' first")
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
			// The variable is emptied rather than left alone, so a shell that
			// set it does not decide what the positive case runs under.
			cmd.Env = append(cmd.Env, "ALETHEIA_RTS_OPTS=")
		}
		out, _ := cmd.CombinedOutput()
		return string(out), cmd.ProcessState.ExitCode()
	}

	t.Run("the cap the binding sets parses", func(t *testing.T) {
		out, code := run(5, "")
		if code != 0 {
			t.Fatalf("the child exited %d under the default cap:\n%s", code, out)
		}
		if !strings.Contains(out, rtsSentinel) {
			t.Fatalf("the child did not reach the end of its work:\n%s", out)
		}
	})

	t.Run("a cap too tight ends the child", func(t *testing.T) {
		out, code := run(1000, "-M12M")
		switch {
		case code == 0:
			t.Fatalf("the child survived a cap it should have crossed:\n%s", out)
		case code == rtsSetupFailed:
			t.Fatalf("the child never got as far as the work:\n%s", out)
		case code == rtsParseFailed:
			t.Fatalf("the definition was refused rather than the heap crossed:\n%s", out)
		}
		if strings.Contains(out, rtsSentinel) {
			t.Fatalf("the child finished its work under a cap it should have crossed:\n%s", out)
		}
		if !strings.Contains(out, rtsAbortMessage) {
			t.Fatalf("the child died without the runtime's abort message, so this is not containment:\n%s", out)
		}
	})
}
