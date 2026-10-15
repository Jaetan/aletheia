// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package main

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"strings"
	"testing"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
)

// runMainEnv makes the test binary run main instead of its tests, for the
// claims about the program's exit status, which only a process of its own
// has. The value "leak" runs main with leakyCycle.
const runMainEnv = "ALETHEIA_STABILITY_RUN_MAIN"

func TestMain(m *testing.M) {
	mode, child := os.LookupEnv(runMainEnv)
	if !child {
		os.Exit(m.Run())
	}
	if mode == "leak" {
		cycle = leakyCycle
	}
	main()
	os.Exit(0)
}

// leakyCycle runs a cycle and then opens a client it never closes: the defect
// the stableptr gate is there to catch.
func leakyCycle(ctx context.Context, backend *aletheia.FFIBackend, dbc aletheia.DBCDefinition, frames int) error {
	if err := runCycle(ctx, backend, dbc, frames); err != nil {
		return err
	}
	_, err := aletheia.NewClient(backend)
	return err
}

// A count variable takes a positive whole number and nothing else, refusing
// every other value by name rather than measuring the default in its place.
func TestEnvCountTakesOnlyPositiveWholeNumbers(t *testing.T) {
	for _, name := range []string{"ALETHEIA_STABILITY_CYCLES", "ALETHEIA_STABILITY_FRAMES"} {
		for _, bad := range []string{"abc", "0", "-3", "5x", "", "99999999999999999999"} {
			t.Setenv(name, bad)
			n, err := envCount(name, 10)
			want := fmt.Sprintf("%s must be a positive whole number, got %q", name, bad)
			if err == nil || err.Error() != want {
				t.Errorf("envCount with %s=%q = %d, %v; want the refusal %q", name, bad, n, err, want)
			}
		}
		for _, good := range []struct {
			raw  string
			want int
		}{{"1", 1}, {"7", 7}} {
			t.Setenv(name, good.raw)
			if n, err := envCount(name, 10); n != good.want || err != nil {
				t.Errorf("envCount with %s=%q = %d, %v; want %d", name, good.raw, n, err, good.want)
			}
		}
		if err := os.Unsetenv(name); err != nil {
			t.Fatalf("os.Unsetenv: %v", err)
		}
		if n, err := envCount(name, 10); n != 10 || err != nil {
			t.Errorf("envCount with %s unset = %d, %v; want the default 10", name, n, err)
		}
	}
}

// Each exact gate fails on a drift of one either way and passes with none, the
// soft one fails only past its cap, and the verdict fails with any gate.
func TestExactGatesCatchAnyDrift(t *testing.T) {
	start := snapshot{RSS: 1 << 20, NumFDs: 5, Goroutines: 3, StablePtrCount: 2}
	checks := gates(start, start)
	if !passed(checks) {
		t.Errorf("two equal snapshots fail: %+v", checks)
	}
	wantGates := [][2]string{
		{"rss", "soft_threshold"}, {"fd_count", "hard_zero"}, {"goroutines", "hard_zero"}, {"stableptr", "hard_zero"},
	}
	if len(checks) != len(wantGates) {
		t.Fatalf("%d checks, want %d: %+v", len(checks), len(wantGates), checks)
	}
	for i, c := range checks {
		if c.Name != wantGates[i][0] || c.Gate != wantGates[i][1] || !c.Passed {
			t.Errorf("with no drift, check %d is %+v; want %s under %s, passed", i, c, wantGates[i][0], wantGates[i][1])
		}
	}

	for _, drift := range []struct {
		name      string
		move      func(*snapshot, int64)
		by        []int64
		threshold int64
	}{
		{"rss", func(s *snapshot, d int64) { s.RSS += d }, []int64{rssDeltaBytesCap + 1, -rssDeltaBytesCap - 1}, rssDeltaBytesCap},
		{"fd_count", func(s *snapshot, d int64) { s.NumFDs += d }, []int64{1, -1}, 0},
		{"goroutines", func(s *snapshot, d int64) { s.Goroutines += d }, []int64{1, -1}, 0},
		{"stableptr", func(s *snapshot, d int64) { s.StablePtrCount += d }, []int64{1, -1}, 0},
	} {
		name := drift.name
		for _, d := range drift.by {
			end := start
			drift.move(&end, d)
			checks := gates(start, end)
			for _, c := range checks {
				if c.Name != name {
					if !c.Passed {
						t.Errorf("drifting %s by %d fails %s too: %+v", name, d, c.Name, c)
					}
					continue
				}
				if c.Passed || c.Delta != d || c.End-c.Start != d || c.Threshold != drift.threshold {
					t.Errorf("drifting %s by %d: %+v; want failed, delta %d, threshold %d", name, d, c, d, drift.threshold)
				}
			}
			if passed(checks) {
				t.Errorf("drifting %s by %d still passes the verdict", name, d)
			}
		}
	}
	for _, d := range []int64{rssDeltaBytesCap, -rssDeltaBytesCap} {
		end := start
		end.RSS += d
		if !passed(gates(start, end)) {
			t.Errorf("an rss drift of %d, at the cap, fails", d)
		}
	}
}

// With ALETHEIA_LIB unset or empty, the kernel is found from the repo root,
// from go/ where tools/stability_run.py runs the harness, and from its own
// directory. The tree is planted, so the answer is the search's alone.
func TestFindLibraryFromEveryDirectoryTheHarnessRunsFrom(t *testing.T) {
	root := t.TempDir()
	planted := filepath.Join(root, "build", "libaletheia-ffi.so")
	own := filepath.Join("go", "benchmarks", "stability")
	if here, err := os.Getwd(); err != nil || !strings.HasSuffix(here, string(filepath.Separator)+own) {
		t.Fatalf("this package is at %q (%v), not under %s as the search assumes", here, err, own)
	}
	for _, dir := range []string{filepath.Dir(planted), filepath.Join(root, own)} {
		if err := os.MkdirAll(dir, 0o755); err != nil {
			t.Fatalf("os.MkdirAll: %v", err)
		}
	}
	if err := os.WriteFile(planted, nil, 0o600); err != nil {
		t.Fatalf("os.WriteFile: %v", err)
	}
	want, err := os.Stat(planted)
	if err != nil {
		t.Fatalf("os.Stat: %v", err)
	}
	for _, dir := range []string{".", "go", own} {
		t.Run(dir, func(t *testing.T) {
			t.Chdir(filepath.Join(root, dir))
			for _, unset := range []bool{true, false} {
				t.Setenv("ALETHEIA_LIB", "")
				if unset {
					if err := os.Unsetenv("ALETHEIA_LIB"); err != nil {
						t.Fatalf("os.Unsetenv: %v", err)
					}
				}
				got := findLibrary()
				if info, err := os.Stat(got); err != nil || !os.SameFile(info, want) {
					t.Errorf("from %s, ALETHEIA_LIB unset %v, the search answered %q, not the planted kernel",
						dir, unset, got)
				}
			}
		})
	}
}

// A cycle closes the client it opens: once it returns, the handles the binding
// holds on the Haskell side are back where they were, which is what the
// stableptr gate reads after a run's cycles.
func TestCycleClosesItsClient(t *testing.T) {
	requireKernel(t)
	lib := findLibrary()
	backend, err := aletheia.NewFFIBackend(lib)
	if err != nil {
		t.Fatalf("loading %s: %v", lib, err)
	}
	before := aletheia.StablePtrCount()
	if err := runCycle(context.Background(), backend, minimalDBC(), 10); err != nil {
		t.Fatalf("runCycle: %v", err)
	}
	if after := aletheia.StablePtrCount(); after != before {
		t.Errorf("handles after a cycle = %d, want %d as before it", after, before)
	}
}

// runProgram runs main in a process of its own in the mode given, stdout
// written to the file at stdoutPath and env added to this process's environment, and answers its exit
// status and its stderr. Both streams are files the child writes itself, so
// nothing copies them beside the test.
func runProgram(t *testing.T, stdoutPath, mode string, env ...string) (int, string) {
	t.Helper()
	stdout, err := os.OpenFile(stdoutPath, os.O_WRONLY|os.O_CREATE|os.O_TRUNC, 0o600)
	if err != nil {
		t.Fatalf("open %s: %v", stdoutPath, err)
	}
	defer func() { _ = stdout.Close() }()
	stderrPath := filepath.Join(t.TempDir(), "stderr")
	stderr, err := os.Create(stderrPath)
	if err != nil {
		t.Fatalf("os.Create: %v", err)
	}
	defer func() { _ = stderr.Close() }()
	cmd := exec.Command(os.Args[0])
	cmd.Env = append(append(os.Environ(), runMainEnv+"="+mode), env...)
	// The race runtime waits a second before a clean exit; nothing here needs it.
	cmd.Env = append(cmd.Env, "GORACE="+os.Getenv("GORACE")+" atexit_sleep_ms=0")
	cmd.Stdout, cmd.Stderr = stdout, stderr
	code := 0
	if err := cmd.Run(); err != nil {
		var exit *exec.ExitError
		if !errors.As(err, &exit) {
			t.Fatalf("running the program: %v", err)
		}
		code = exit.ExitCode()
	}
	written, err := os.ReadFile(stderrPath)
	if err != nil {
		t.Fatalf("reading the program's stderr: %v", err)
	}
	return code, string(written)
}

// requireKernel skips the rest of a test when this build cannot load the
// kernel or there is none to load.
func requireKernel(t *testing.T) {
	t.Helper()
	if !cgoEnabled {
		t.Skip("built without cgo; the binding cannot load the library")
	}
	if _, err := os.Stat(findLibrary()); err != nil {
		t.Skip("libaletheia-ffi.so not built; run 'cabal run shake -- build'")
	}
}

// readReport decodes the report the program wrote to path.
func readReport(t *testing.T, path string) report {
	t.Helper()
	written, err := os.ReadFile(path)
	if err != nil {
		t.Fatalf("reading the report: %v", err)
	}
	var r report
	if err := json.Unmarshal(written, &r); err != nil {
		t.Fatalf("the report %q is not JSON: %v", written, err)
	}
	return r
}

// The exit status is what tools/stability_run.py reads: 0 when every gate
// passed, 1 when one failed and the verdict is in the report, and anything
// else, 2 from this harness, for a failure with no verdict. A refused count
// exits 2 before the kernel loads, the library pointed at nothing so a check
// moved after the load names the load instead. Against the kernel, found by
// main's own search with ALETHEIA_LIB empty, a short run exits 0, one whose
// every cycle leaves a client open exits 1 with the stableptr gate failed,
// and a report that cannot be written exits 2 naming it.
func TestProgramExitStatus(t *testing.T) {
	dir := t.TempDir()
	absent := "ALETHEIA_LIB=" + filepath.Join(dir, "absent.so")
	for _, name := range []string{"ALETHEIA_STABILITY_CYCLES", "ALETHEIA_STABILITY_FRAMES"} {
		t.Run(name+" refused", func(t *testing.T) {
			out := filepath.Join(dir, name+".json")
			code, stderr := runProgram(t, out, "", absent, name+"=abc")
			if code != 2 || !strings.Contains(stderr, name+" must be a positive whole number") {
				t.Errorf("%s=abc exits %d with stderr %q; want 2 and the variable named", name, code, stderr)
			}
			if written, err := os.ReadFile(out); err != nil || len(written) != 0 {
				t.Errorf("a refused run wrote %q (%v), want nothing", written, err)
			}
		})
	}
	short := []string{"ALETHEIA_LIB=", "ALETHEIA_STABILITY_CYCLES=2", "ALETHEIA_STABILITY_FRAMES=10"}
	t.Run("a short run passes", func(t *testing.T) {
		requireKernel(t)
		out := filepath.Join(dir, "short.json")
		if code, stderr := runProgram(t, out, "", short...); code != 0 {
			t.Fatalf("a short run exits %d with stderr %q, want 0", code, stderr)
		}
		if r := readReport(t, out); !r.Passed {
			t.Errorf("a short run's report fails: %+v", r)
		}
	})
	t.Run("a leak fails the stableptr gate", func(t *testing.T) {
		requireKernel(t)
		out := filepath.Join(dir, "leak.json")
		if code, stderr := runProgram(t, out, "leak", short...); code != 1 {
			t.Fatalf("a run leaking a client per cycle exits %d with stderr %q, want 1", code, stderr)
		}
		r := readReport(t, out)
		i := slices.IndexFunc(r.SubChecks, func(c subCheck) bool { return c.Name == "stableptr" })
		if i < 0 || r.SubChecks[i].Passed || r.SubChecks[i].Delta != 2 {
			t.Errorf("two leaked clients read as %+v, want stableptr failed with delta 2", r.SubChecks)
		}
		if r.Passed {
			t.Errorf("a run leaking a client per cycle passes: %+v", r)
		}
	})
	t.Run("a report that cannot be written", func(t *testing.T) {
		requireKernel(t)
		code, stderr := runProgram(t, "/dev/full", "", short...)
		if code != 2 || !strings.Contains(stderr, "writing the report failed") {
			t.Errorf("a report to /dev/full exits %d with stderr %q; want 2 and the write named", code, stderr)
		}
	})
}
