//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// A command holding one long number is refused, and the process that sent it
// lives. The kernel refuses a JSON number whose rational components pass the
// signed 64-bit range, and its refusal reports the measured magnitude up to
// 2^64-1 and that ceiling past it, with "at least" before the ceiling in the
// message. A command of about 100 KB whose one number has 100,001 digits gets
// that refusal. The command is sent from a child, this same binary run again
// with a variable set: a kernel that echoes the number whole ends the process
// that called it, so the parent reads the child's reply and exit status
// rather than sharing its end.

package aletheia

import (
	"bytes"
	"errors"
	"fmt"
	"math"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

const (
	literalChildEnv  = "ALETHEIA_LITERAL_BOUND_CHILD"
	literalChildTest = "^TestLongLiteralRefusedAtTheCeiling$"

	// literalZeros is the digits after the leading 1 of the command's one
	// number.
	literalZeros = 100000

	// literalSetupFailed is the child's exit when the library or its state
	// would not open, and literalCallFailed when the call returned an error
	// rather than a reply. Neither is the end under test, so both are named.
	literalSetupFailed = 2
	literalCallFailed  = 3
)

// runLiteralChild is the child: send the command through the raw entry and
// write the reply to stdout. It always exits.
func runLiteralChild() {
	backend, err := NewFFIBackend(os.Getenv("ALETHEIA_LIB"))
	if err != nil {
		fmt.Fprintln(os.Stderr, "child backend:", err)
		os.Exit(literalSetupFailed)
	}
	state, err := backend.Init()
	if err != nil {
		fmt.Fprintln(os.Stderr, "child state:", err)
		os.Exit(literalSetupFailed)
	}
	command := `{"type": "command", "command": "startStream", "x": 1` + strings.Repeat("0", literalZeros) + "}"
	reply, err := backend.Process(state, command)
	backend.Close(state)
	if err != nil {
		fmt.Fprintln(os.Stderr, "child call:", err)
		os.Exit(literalCallFailed)
	}
	fmt.Print(reply)
	os.Exit(0)
}

func TestLongLiteralRefusedAtTheCeiling(t *testing.T) {
	if os.Getenv(literalChildEnv) == "1" {
		runLiteralChild()
		return // unreachable: runLiteralChild always exits
	}

	lib := findFFILibrary()
	if lib == "" {
		t.Skip("libaletheia-ffi.so not found; run 'cabal run shake -- build' first")
	}
	absLib, err := filepath.Abs(lib)
	if err != nil {
		t.Fatalf("abs lib path: %v", err)
	}

	cmd := exec.Command(os.Args[0], "-test.run="+literalChildTest)
	// The runtime flags are emptied rather than left alone, so a shell that
	// set them does not decide what the child runs under.
	cmd.Env = append(os.Environ(), literalChildEnv+"=1", "ALETHEIA_LIB="+absLib, rtsOverrideEnv+"=")
	var stdout, stderr bytes.Buffer
	cmd.Stdout = &stdout
	cmd.Stderr = &stderr
	if err := cmd.Run(); err != nil {
		t.Fatalf("the child ended with %v:\n%s", err, stderr.String())
	}

	_, err = decodeResponse(stdout.String(), "success")
	var bex *InputBoundExceededError
	if !errors.As(err, &bex) {
		t.Fatalf("the reply is not a bound refusal: %v", err)
	}
	want := InputBoundExceededError{
		BoundKind: BoundKindRationalComponentMagnitude,
		Observed:  math.MaxUint64,
		Limit:     MaxRationalComponentMagnitude,
		Code:      CodeInputBoundExceeded,
		Message: fmt.Sprintf("rational component magnitude at least %d exceeds limit %d",
			uint64(math.MaxUint64), MaxRationalComponentMagnitude),
	}
	if *bex != want {
		t.Fatalf("refusal = %+v, want %+v", *bex, want)
	}
}
