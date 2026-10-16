// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package main

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"slices"
	"strings"
	"testing"
)

// runMainEnv makes the test binary run main instead of its tests, for the
// claims about the program's exit status, which only a process of its own
// has.
const runMainEnv = "ALETHEIA_BENCHMARK_RUN_MAIN"

func TestMain(m *testing.M) {
	if _, child := os.LookupEnv(runMainEnv); child {
		main()
		os.Exit(0)
	}
	os.Exit(m.Run())
}

// The lane tests drive the throughput lane with an operation of their own, a
// failing lane being one that cannot be made from outside a real one.

var errRefused = errors.New("kernel refused the frame")

func TestThroughputLaneAbortsOnAFailedWarmup(t *testing.T) {
	var calls []int
	run := func(n int) (float64, error) {
		calls = append(calls, n)
		return 0, errRefused
	}
	var out bytes.Buffer
	_, err := throughputLane(&out, "Stream LTL", run, 100, 3, 2)
	if err == nil {
		t.Fatal("a failed warmup returned no error")
	}
	for _, want := range []string{`lane "Stream LTL"`, "warmup 1/2", errRefused.Error()} {
		if !strings.Contains(err.Error(), want) {
			t.Errorf("error %q does not name %q", err, want)
		}
	}
	if !errors.Is(err, errRefused) {
		t.Errorf("error %q does not wrap the operation's", err)
	}
	if !slices.Equal(calls, []int{10}) {
		t.Errorf("calls after the failed warmup: %v, want the one warmup pass over a tenth of the frames", calls)
	}
	if strings.Contains(out.String(), "Run 1/") {
		t.Errorf("a measured run was printed after the failed warmup:\n%s", out.String())
	}
}

func TestThroughputLaneNamesTheFailedRun(t *testing.T) {
	var calls []int
	run := func(n int) (float64, error) {
		calls = append(calls, n)
		if len(calls) == 4 {
			return 0, errRefused
		}
		return 1000, nil
	}
	var out bytes.Buffer
	_, err := throughputLane(&out, "Frame Building", run, 100, 3, 2)
	if err == nil {
		t.Fatal("a failed measured run returned no error")
	}
	for _, want := range []string{`lane "Frame Building"`, "run 2/3", errRefused.Error()} {
		if !strings.Contains(err.Error(), want) {
			t.Errorf("error %q does not name %q", err, want)
		}
	}
	if !slices.Equal(calls, []int{10, 10, 100, 100}) {
		t.Errorf("calls: %v, want two warmup passes and the two runs up to the failure", calls)
	}
}

func TestThroughputLaneMeasuresEveryRun(t *testing.T) {
	var calls []int
	run := func(n int) (float64, error) {
		calls = append(calls, n)
		return float64(1000 + len(calls)), nil
	}
	var out bytes.Buffer
	r, err := throughputLane(&out, "Signal Extraction", run, 100, 3, 2)
	if err != nil {
		t.Fatalf("a healthy lane failed: %v", err)
	}
	if !slices.Equal(calls, []int{10, 10, 100, 100, 100}) {
		t.Errorf("calls: %v, want two warmup passes then three runs", calls)
	}
	if r.Name != "Signal Extraction" || r.Frames != 100 || r.Runs != 3 {
		t.Errorf("result names the lane wrong: %+v", r)
	}
	if r.FPSMin != 1003 || r.FPSMax != 1005 || r.FPSMean != 1004 {
		t.Errorf("result statistics are not the runs' (1003, 1004, 1005): %+v", r)
	}
	for _, want := range []string{"Signal Extraction:", "Run 1/3: 1003 ops/sec", "Run 3/3: 1005 ops/sec"} {
		if !strings.Contains(out.String(), want) {
			t.Errorf("output lacks %q:\n%s", want, out.String())
		}
	}
}

// A count that measures nothing is refused by name, and one of each with no
// warmup is taken, warming up being a choice.
func TestCountsRefuseWhatMeasuresNothing(t *testing.T) {
	for _, c := range []struct {
		frames, runs, ops, warmup int
		want                      string
	}{
		{0, 5, 5000, 2, "--frames must be at least 1, got 0"},
		{-100, 5, 5000, 2, "--frames must be at least 1, got -100"},
		{10000, 0, 5000, 2, "--runs must be at least 1, got 0"},
		{10000, 5, 0, 2, "--ops must be at least 1, got 0"},
		{10000, 5, 5000, -1, "--warmup must not be negative, got -1"},
	} {
		err := checkCounts(c.frames, c.runs, c.ops, c.warmup)
		if err == nil || err.Error() != c.want {
			t.Errorf("checkCounts(%d, %d, %d, %d) = %v, want %q", c.frames, c.runs, c.ops, c.warmup, err, c.want)
		}
	}
	if err := checkCounts(1, 1, 1, 0); err != nil {
		t.Errorf("checkCounts(1, 1, 1, 0) = %v, want nil", err)
	}
}

var errFull = errors.New("no space left on device")

// fullWriter refuses every write, as /dev/full does.
type fullWriter struct{}

func (fullWriter) Write([]byte) (int, error) { return 0, errFull }

// A report that cannot be written is an error naming it and wrapping the
// write's, and one that can is written whole.
func TestReportWriteFailureIsAnError(t *testing.T) {
	out := jsonOutput{
		Benchmark: "throughput", Language: "go", Timestamp: "2026-01-02T03:04:05Z",
		Parameters: throughputParameters{Frames: 10, Runs: 1, Warmup: 0},
		Results:    []throughputResult{},
	}
	err := writeReport(fullWriter{}, out)
	if err == nil {
		t.Fatal("a report that could not be written returned no error")
	}
	if !strings.Contains(err.Error(), "writing the throughput report failed") || !errors.Is(err, errFull) {
		t.Errorf("error %q does not name the report and wrap the write's", err)
	}
	var buf bytes.Buffer
	if err := writeReport(&buf, out); err != nil {
		t.Fatalf("writing to a buffer failed: %v", err)
	}
	want, err := json.MarshalIndent(out, "", "  ")
	if err != nil {
		t.Fatalf("json.MarshalIndent: %v", err)
	}
	if got := buf.String(); got != string(want)+"\n" {
		t.Errorf("report written:\n%s\nwant:\n%s", got, want)
	}
}

// The text report's writer passes writes through until one fails, keeps that
// error, and lets no later write reach the stream, so the report it names as
// failed carries the first failed write's error.
func TestReportWriterKeepsTheFirstError(t *testing.T) {
	var before, after bytes.Buffer
	w := &reportWriter{w: &before}
	if _, err := fmt.Fprint(w, "written"); err != nil || w.check("latency") != nil {
		t.Fatalf("a write to a buffer failed: %v, %v", err, w.check("latency"))
	}
	w.w = fullWriter{}
	if _, err := fmt.Fprint(w, "refused"); !errors.Is(err, errFull) {
		t.Errorf("a refused write answered %v, want the stream's error", err)
	}
	w.w = &after
	if _, err := fmt.Fprint(w, "dropped"); !errors.Is(err, errFull) {
		t.Errorf("a write after the refused one answered %v, want the first error", err)
	}
	if before.String() != "written" || after.Len() != 0 {
		t.Errorf("the streams hold %q and %q, want the write before the failure and nothing after it",
			before.String(), after.String())
	}
	err := w.check("latency")
	if err == nil || !strings.Contains(err.Error(), "writing the latency report failed") || !errors.Is(err, errFull) {
		t.Errorf("error %v does not name the report and wrap the write's", err)
	}
}

// With ALETHEIA_LIB unset or empty, the kernel is found from each directory
// the benchmark is run from: the repo root, its own, and the one the usage
// line in main.go names. The tree is planted, so the answer is the search's
// alone.
func TestFindLibraryFromEveryDocumentedDirectory(t *testing.T) {
	src, err := os.ReadFile("main.go")
	if err != nil {
		t.Fatalf("reading main.go: %v", err)
	}
	usage := regexp.MustCompile(`(?m)^//\s+cd (\S+) && go run (\S+) `).FindSubmatch(src)
	if usage == nil {
		t.Fatal("main.go carries no usage line of the form cd <dir> && go run <package>")
	}
	own := filepath.Join("go", "benchmarks")
	if here, err := os.Getwd(); err != nil || !strings.HasSuffix(here, string(filepath.Separator)+own) {
		t.Fatalf("this package is at %q (%v), not under %s as the search assumes", here, err, own)
	}
	usageDir := string(usage[1])
	if got := filepath.Join(usageDir, string(usage[2])); got != own {
		t.Fatalf("the usage line runs %s, which is not this package", got)
	}

	root := t.TempDir()
	planted := filepath.Join(root, "build", "libaletheia-ffi.so")
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
	for _, dir := range []string{".", usageDir, own} {
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

// runProgram runs main from this test binary, in this process's working
// directory.
func runProgram(t *testing.T, stdoutPath string, env []string, args ...string) (int, string) {
	t.Helper()
	return runBinary(t, os.Args[0], "", stdoutPath, env, args...)
}

// runBinary runs main in a process of its own from binary, this test binary or
// a copy of it, in the working directory dir ("" for this process's own),
// stdout written to the file at stdoutPath and env added to this process's
// environment, and answers its exit status and its stderr. Both streams are
// files the child writes itself, so nothing copies them beside the test.
func runBinary(t *testing.T, binary, dir, stdoutPath string, env []string, args ...string) (int, string) {
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
	cmd := exec.Command(binary, args...)
	cmd.Dir = dir
	cmd.Env = append(append(os.Environ(), runMainEnv+"=1"), env...)
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

// The exit status is what benchmarks/run_all.sh reads to tell a run from a
// failure. Each count that measures nothing, whichever mode reads it, an
// unknown mode and an argument the flags leave over exit 1 before the kernel
// loads, the library pointed at nothing so a check moved after the load names
// the load instead. A kernel that does not load exits 1 naming the path, and
// with ALETHEIA_LIB empty that path is the working directory's candidate even
// where the binary sits beside a build tree; neither writes a report. Against
// the kernel, found by main's own search with ALETHEIA_LIB empty, a report
// that cannot be written, JSON or text, exits 1 naming it, and one that can
// is written and exits 0.
func TestProgramExitStatus(t *testing.T) {
	dir := t.TempDir()
	absent := filepath.Join(dir, "absent.so")
	for i, refused := range []struct {
		args []string
		want string
	}{
		{[]string{"throughput", "--frames", "0", "--runs", "1", "--warmup", "0"}, "--frames must be at least 1, got 0"},
		{[]string{"throughput", "--frames", "-100", "--runs", "1", "--warmup", "0"}, "--frames must be at least 1, got -100"},
		{[]string{"throughput", "--frames", "100", "--runs", "0", "--warmup", "0"}, "--runs must be at least 1, got 0"},
		{[]string{"latency", "--ops", "0", "--warmup", "0"}, "--ops must be at least 1, got 0"},
		{[]string{"scaling", "--quick", "--runs", "0"}, "--runs must be at least 1, got 0"},
		{[]string{"throughput", "--frames", "100", "--runs", "1", "--warmup", "-1"}, "--warmup must not be negative, got -1"},
		{[]string{"thruput", "--frames", "10", "--runs", "1"}, `unknown mode "thruput", expected throughput, latency or scaling`},
		{[]string{"--frames", "10", "latency"}, `unexpected argument "latency"`},
		{[]string{"latency", "--ops", "10", "--"}, `unexpected argument "--json"`},
	} {
		t.Run(strings.Join(refused.args, " "), func(t *testing.T) {
			out := filepath.Join(dir, fmt.Sprintf("refused-%d.json", i))
			code, stderr := runProgram(t, out, []string{"ALETHEIA_LIB=" + absent},
				append(refused.args, "--json")...)
			if code != 1 || !strings.Contains(stderr, refused.want) {
				t.Errorf("%v exits %d with stderr %q; want 1 and %q", refused.args, code, stderr, refused.want)
			}
			if written, err := os.ReadFile(out); err != nil || len(written) != 0 {
				t.Errorf("a refused run wrote %q (%v), want nothing", written, err)
			}
		})
	}
	text := []string{"throughput", "--frames", "10", "--runs", "1", "--warmup", "0"}
	args := slices.Concat(text, []string{"--json"})
	t.Run("a kernel that does not load", func(t *testing.T) {
		out := filepath.Join(dir, "unloaded.json")
		code, stderr := runProgram(t, out, []string{"ALETHEIA_LIB=" + absent}, args...)
		if want := "benchmark: loading " + absent + " failed: "; code != 1 || !strings.Contains(stderr, want) {
			t.Errorf("a run against %s exits %d with stderr %q; want 1 and %q", absent, code, stderr, want)
		}
		if written, err := os.ReadFile(out); err != nil || len(written) != 0 {
			t.Errorf("a run whose kernel did not load wrote %q (%v), want nothing", written, err)
		}
	})
	t.Run("the search starts from the working directory, not the binary", func(t *testing.T) {
		root := t.TempDir()
		binary := filepath.Join(root, "go", "benchmarks", "benchmarks")
		copyTestBinary(t, binary)
		planted := filepath.Join(root, "build", "libaletheia-ffi.so")
		if err := os.MkdirAll(filepath.Dir(planted), 0o755); err != nil {
			t.Fatalf("os.MkdirAll: %v", err)
		}
		if err := os.WriteFile(planted, nil, 0o600); err != nil {
			t.Fatalf("os.WriteFile: %v", err)
		}
		// Two levels deep, so every candidate the search reads lies under a
		// directory of this test's own, with no build tree in it.
		elsewhere := filepath.Join(t.TempDir(), "a", "b")
		if err := os.MkdirAll(elsewhere, 0o755); err != nil {
			t.Fatalf("os.MkdirAll: %v", err)
		}
		out := filepath.Join(dir, "elsewhere.json")
		code, stderr := runBinary(t, binary, elsewhere, out, []string{"ALETHEIA_LIB="}, args...)
		want := "benchmark: loading " + filepath.Join("..", "..", "build", "libaletheia-ffi.so") + " failed: "
		if code != 1 || !strings.Contains(stderr, want) || strings.Contains(stderr, root) {
			t.Errorf("a binary beside %s run from %s exits %d with stderr %q; want 1 and %q", planted, elsewhere, code, stderr, want)
		}
		if written, err := os.ReadFile(out); err != nil || len(written) != 0 {
			t.Errorf("a run whose kernel did not load wrote %q (%v), want nothing", written, err)
		}
	})
	searched := []string{"ALETHEIA_LIB="}
	t.Run("a report that cannot be written", func(t *testing.T) {
		requireKernel(t)
		code, stderr := runProgram(t, "/dev/full", searched, args...)
		if code != 1 || !strings.Contains(stderr, "writing the throughput report failed") {
			t.Errorf("a report to /dev/full exits %d with stderr %q; want 1 and the write named", code, stderr)
		}
	})
	t.Run("a text report that cannot be written", func(t *testing.T) {
		requireKernel(t)
		code, stderr := runProgram(t, "/dev/full", searched, text...)
		if code != 1 || !strings.Contains(stderr, "writing the throughput report failed: write /dev/stdout: no space left on device") {
			t.Errorf("a text report to /dev/full exits %d with stderr %q; want 1 and the write named", code, stderr)
		}
	})
	t.Run("a report written", func(t *testing.T) {
		requireKernel(t)
		out := filepath.Join(dir, "report.json")
		code, stderr := runProgram(t, out, searched, args...)
		if code != 0 {
			t.Fatalf("a run of ten frames exits %d with stderr %q, want 0", code, stderr)
		}
		written, err := os.ReadFile(out)
		if err != nil {
			t.Fatalf("reading the report: %v", err)
		}
		var report struct {
			Benchmark string             `json:"benchmark"`
			Results   []throughputResult `json:"results"`
		}
		if err := json.Unmarshal(written, &report); err != nil || report.Benchmark != "throughput" || len(report.Results) == 0 {
			t.Errorf("the report %q (%v) is not a throughput report with results", written, err)
		}
	})
}
