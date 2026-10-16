// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package main

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"math"
	"os"
	"os/exec"
	"path/filepath"
	"runtime/metrics"
	"slices"
	"strconv"
	"strings"
	"testing"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
)

// runMainEnv makes the test binary run main instead of its tests, for the
// claims about the program's exit status, which only a process of its own
// has. Its value names the cycle or the snapshot main runs with; the empty
// value runs main as it is.
const runMainEnv = "ALETHEIA_STABILITY_RUN_MAIN"

func TestMain(m *testing.M) {
	mode, child := os.LookupEnv(runMainEnv)
	if !child {
		os.Exit(m.Run())
	}
	switch mode {
	case "leak":
		cycle = leakyCycle
	case "warm-up fails":
		cycle = failingCycle(1)
	case "cycle fails":
		cycle = failingCycle(2)
	case "opening snapshot fails":
		snapshotOf = failingSnapshot(1)
	case "closing snapshot fails":
		snapshotOf = failingSnapshot(2)
	}
	main()
	os.Exit(0)
}

var (
	errCycle    = errors.New("the kernel refused the frame")
	errSnapshot = errors.New("/proc/self/fd is gone")
)

// failingCycle answers a cycle that fails on its nth call, the warm-up being
// the first, and runs every call before it.
func failingCycle(nth int) func(context.Context, *aletheia.FFIBackend, aletheia.DBCDefinition, int) error {
	calls := 0
	return func(ctx context.Context, backend *aletheia.FFIBackend, dbc aletheia.DBCDefinition, frames int) error {
		calls++
		if calls == nth {
			return errCycle
		}
		return runCycle(ctx, backend, dbc, frames)
	}
}

// failingSnapshot answers a snapshot that fails on its nth call, the opening
// one being the first, and takes every one before it.
func failingSnapshot(nth int) func(string) (snapshot, error) {
	calls := 0
	return func(metric string) (snapshot, error) {
		calls++
		if calls == nth {
			return snapshot{}, errSnapshot
		}
		return takeSnapshot(metric)
	}
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

// A count variable takes ASCII digits only, from 1 to 2147483647, and refuses
// every other value by name rather than measuring the default in its place.
func TestEnvCountTakesOnlyWholeNumbersFromOneToMaxInt32(t *testing.T) {
	for _, name := range []string{"ALETHEIA_STABILITY_CYCLES", "ALETHEIA_STABILITY_FRAMES"} {
		for _, bad := range []string{"abc", "0", "-3", "+5", "5x", "", "2147483648", "99999999999999999999"} {
			t.Setenv(name, bad)
			n, err := envCount(name, 10)
			want := fmt.Sprintf("%s must be a whole number from 1 to 2147483647, got %q", name, bad)
			if err == nil || err.Error() != want {
				t.Errorf("envCount with %s=%q = %d, %v; want the refusal %q", name, bad, n, err, want)
			}
		}
		for _, good := range []struct {
			raw  string
			want int
		}{{"1", 1}, {"7", 7}, {"2147483647", 2147483647}} {
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

// A snapshot's heap is the runtime's count of live heap bytes, never zero in a
// running program.
func TestSnapshotReadsTheHeap(t *testing.T) {
	if s, err := takeSnapshot(heapMetric); err != nil || s.RSS <= 0 {
		t.Errorf("takeSnapshot(%q) = %+v, %v; want a positive heap", heapMetric, s, err)
	}
}

// A metric a snapshot cannot read as a count of bytes is an error naming the
// metric and what it is instead, never a zero both snapshots agree on.
func TestSnapshotRefusesWhatIsNotACountOfBytes(t *testing.T) {
	for _, c := range []struct{ metric, want string }{
		{"/no/such/metric:bytes", "not a metric this Go supports"},
		{"/gc/heap/allocs-by-size:bytes", "a float64 histogram, not a count of bytes"},
	} {
		s, err := takeSnapshot(c.metric)
		if err == nil || !strings.Contains(err.Error(), c.metric) || !strings.Contains(err.Error(), c.want) {
			t.Errorf("takeSnapshot(%q) = %+v, %v; want an error naming it and %q", c.metric, s, err, c.want)
		}
	}
}

// Every kind of value this Go's runtime/metrics describes has a name for the
// refusal to give.
func TestEveryMetricKindHasAName(t *testing.T) {
	reported := map[metrics.ValueKind]bool{}
	for _, d := range metrics.All() {
		if kindNames[d.Kind] == "" && !reported[d.Kind] {
			reported[d.Kind] = true
			t.Errorf("%s is of kind %d, which kindNames does not name", d.Name, d.Kind)
		}
	}
}

// A count of bytes converts exactly up to math.MaxInt64 and is refused past
// it, and the rss gate compares a count at the bound with zero either way
// without wrapping.
func TestByteCountTakesEveryInt64(t *testing.T) {
	for _, v := range []uint64{0, 1<<62 + 1, math.MaxInt64} {
		if n, err := byteCount(v); err != nil || uint64(n) != v {
			t.Errorf("byteCount(%d) = %d, %v; want it unchanged", v, n, err)
		}
	}
	for _, v := range []uint64{math.MaxInt64 + 1, math.MaxUint64} {
		if n, err := byteCount(v); err == nil || !strings.Contains(err.Error(), strconv.FormatUint(v, 10)) {
			t.Errorf("byteCount(%d) = %d, %v; want a refusal naming it", v, n, err)
		}
	}
	for _, c := range []struct{ start, end, delta int64 }{{0, math.MaxInt64, math.MaxInt64}, {math.MaxInt64, 0, -math.MaxInt64}} {
		rss := gates(snapshot{RSS: c.start}, snapshot{RSS: c.end})[0]
		if rss.Name != "rss" || rss.Passed || rss.Delta != c.delta {
			t.Errorf("rss from %d to %d reads %+v; want failed with delta %d", c.start, c.end, rss, c.delta)
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

// runProgram runs main from this test binary, in this process's working
// directory.
func runProgram(t *testing.T, stdoutPath, mode string, env ...string) (int, string) {
	t.Helper()
	return runBinary(t, os.Args[0], "", stdoutPath, mode, env...)
}

// runBinary runs main in a process of its own from binary, this test binary or
// a copy of it, in the working directory dir ("" for this process's own) and in
// the mode given, stdout written to the file at stdoutPath and env added to this
// process's environment, and answers its exit status and its stderr. Both
// streams are files the child writes itself, so nothing copies them beside the
// test.
func runBinary(t *testing.T, binary, dir, stdoutPath, mode string, env ...string) (int, string) {
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
	cmd := exec.Command(binary)
	cmd.Dir = dir
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

// copyTestBinary copies this test binary to path, creating its directory. A
// copy rather than a link, since os.Executable answers the file a link
// resolves to.
func copyTestBinary(t *testing.T, path string) {
	t.Helper()
	binary, err := os.ReadFile(os.Args[0])
	if err != nil {
		t.Fatalf("reading the test binary: %v", err)
	}
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		t.Fatalf("os.MkdirAll: %v", err)
	}
	if err := os.WriteFile(path, binary, 0o700); err != nil {
		t.Fatalf("os.WriteFile: %v", err)
	}
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
// moved after the load names the load instead. A kernel that does not load
// exits 2 naming the path, and with ALETHEIA_LIB empty that path is the
// working directory's candidate even where the binary sits beside a build
// tree. Against the kernel, found by main's own search with ALETHEIA_LIB
// empty, a short run exits 0, one whose every cycle leaves a client open
// exits 1 with the stableptr gate failed, and a failed warm-up, cycle or
// snapshot and a report that cannot be written exit 2 naming the failure. A
// run with no verdict writes nothing to stdout.
func TestProgramExitStatus(t *testing.T) {
	dir := t.TempDir()
	absentPath := filepath.Join(dir, "absent.so")
	absent := "ALETHEIA_LIB=" + absentPath
	counts := []string{"ALETHEIA_STABILITY_CYCLES=2", "ALETHEIA_STABILITY_FRAMES=10"}
	for _, name := range []string{"ALETHEIA_STABILITY_CYCLES", "ALETHEIA_STABILITY_FRAMES"} {
		for _, value := range []string{"abc", "+5", "2147483648"} {
			t.Run(name+"="+value+" refused", func(t *testing.T) {
				out := filepath.Join(dir, name+value+".json")
				code, stderr := runProgram(t, out, "", absent, name+"="+value)
				want := "stability: " + name + " must be a whole number from 1 to 2147483647, got " + strconv.Quote(value) + "\n"
				if code != 2 || stderr != want {
					t.Errorf("%s=%s exits %d with stderr %q; want 2 and %q", name, value, code, stderr, want)
				}
				if written, err := os.ReadFile(out); err != nil || len(written) != 0 {
					t.Errorf("a refused run wrote %q (%v), want nothing", written, err)
				}
			})
		}
	}
	t.Run("a kernel that does not load", func(t *testing.T) {
		out := filepath.Join(dir, "unloaded.json")
		code, stderr := runProgram(t, out, "", slices.Concat(counts, []string{absent})...)
		if want := "stability: loading " + absentPath + " failed: "; code != 2 || !strings.HasPrefix(stderr, want) {
			t.Errorf("a run against %s exits %d with stderr %q; want 2 and %q", absentPath, code, stderr, want)
		}
		if written, err := os.ReadFile(out); err != nil || len(written) != 0 {
			t.Errorf("a run whose kernel did not load wrote %q (%v), want nothing", written, err)
		}
	})
	t.Run("the search starts from the working directory, not the binary", func(t *testing.T) {
		root := t.TempDir()
		binary := filepath.Join(root, "go", "benchmarks", "stability", "stability")
		copyTestBinary(t, binary)
		planted := filepath.Join(root, "build", "libaletheia-ffi.so")
		if err := os.MkdirAll(filepath.Dir(planted), 0o755); err != nil {
			t.Fatalf("os.MkdirAll: %v", err)
		}
		if err := os.WriteFile(planted, nil, 0o600); err != nil {
			t.Fatalf("os.WriteFile: %v", err)
		}
		// Three levels deep, so every candidate the search reads lies under a
		// directory of this test's own, with no build tree in it.
		elsewhere := filepath.Join(t.TempDir(), "a", "b", "c")
		if err := os.MkdirAll(elsewhere, 0o755); err != nil {
			t.Fatalf("os.MkdirAll: %v", err)
		}
		out := filepath.Join(dir, "elsewhere.json")
		code, stderr := runBinary(t, binary, elsewhere, out, "", slices.Concat(counts, []string{"ALETHEIA_LIB="})...)
		want := "stability: loading " + filepath.Join("..", "..", "..", "build", "libaletheia-ffi.so") + " failed: "
		if code != 2 || !strings.HasPrefix(stderr, want) || strings.Contains(stderr, root) {
			t.Errorf("a binary beside %s run from %s exits %d with stderr %q; want 2 and %q", planted, elsewhere, code, stderr, want)
		}
		if written, err := os.ReadFile(out); err != nil || len(written) != 0 {
			t.Errorf("a run whose kernel did not load wrote %q (%v), want nothing", written, err)
		}
	})
	short := slices.Concat([]string{"ALETHEIA_LIB="}, counts)
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
	for _, failed := range []struct{ mode, line string }{
		{"warm-up fails", "the warm-up cycle failed: " + errCycle.Error()},
		{"cycle fails", "cycle 1 of 2 failed: " + errCycle.Error()},
		{"opening snapshot fails", "the opening snapshot failed: " + errSnapshot.Error()},
		{"closing snapshot fails", "the closing snapshot failed: " + errSnapshot.Error()},
	} {
		t.Run(failed.mode, func(t *testing.T) {
			requireKernel(t)
			out := filepath.Join(dir, failed.mode+".json")
			code, stderr := runProgram(t, out, failed.mode, short...)
			if want := "stability: " + failed.line + "\n"; code != 2 || stderr != want {
				t.Errorf("a run where the %s exits %d with stderr %q; want 2 and %q", failed.mode, code, stderr, want)
			}
			if written, err := os.ReadFile(out); err != nil || len(written) != 0 {
				t.Errorf("a run where the %s wrote %q (%v), want nothing", failed.mode, written, err)
			}
		})
	}
	t.Run("a report that cannot be written", func(t *testing.T) {
		requireKernel(t)
		code, stderr := runProgram(t, "/dev/full", "", short...)
		if code != 2 || !strings.Contains(stderr, "writing the report failed") {
			t.Errorf("a report to /dev/full exits %d with stderr %q; want 2 and the write named", code, stderr)
		}
	})
}
