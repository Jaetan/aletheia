//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"errors"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// loaderScenarioEnv names the scenario a child process runs. Each scenario
// opens a library the parent cannot: the runtime starts once per process, on
// the library the renderer and the decimal parser then call, so the state
// each scenario reads exists only in a fresh process.
const loaderScenarioEnv = "ALETHEIA_TEST_LOADER_SCENARIO"

// standIn is the stand-in kernel the build makes beside the library: every
// one is built by `cabal run shake -- build`, so a library found without its
// stand-ins is a build that has not run since they were added.
func standIn(t *testing.T, lib, name string) string {
	t.Helper()
	path := filepath.Join(filepath.Dir(lib), "stand-ins", name+".so")
	if _, err := os.Stat(path); err != nil {
		t.Fatalf("stand-in %s not built beside %s (%v); run 'cabal run shake -- build'", name, lib, err)
	}
	return path
}

// runLoaderChild re-runs this binary on one scenario with the library named,
// or with ALETHEIA_LIB removed where the scenario is the search itself, and
// answers what the child printed.
func runLoaderChild(t *testing.T, scenario, lib, dir string) string {
	t.Helper()
	var extra []string
	if lib != "" {
		extra = append(extra, "ALETHEIA_LIB="+lib)
	}
	return runScenarioChild(t, "TestLoaderFailuresAreVocal", scenario, dir, extra...)
}

// runScenarioChild re-runs this binary's test named on one scenario, in dir
// when it is not empty, with the runtime's start suppressed, ALETHEIA_LIB
// removed and the variables extra names set, and answers what the child
// printed.
func runScenarioChild(t *testing.T, test, scenario, dir string, extra ...string) string {
	t.Helper()
	exe, err := os.Executable()
	if err != nil {
		t.Fatalf("the test binary's own path: %v", err)
	}
	cmd := exec.Command(exe, "-test.run=^"+test+"$", "-test.v")
	cmd.Dir = dir
	env := make([]string, 0, len(os.Environ())+2+len(extra))
	for _, e := range os.Environ() {
		if strings.HasPrefix(e, "ALETHEIA_LIB=") || strings.HasPrefix(e, skipRTSInitEnv+"=") || strings.HasPrefix(e, loaderScenarioEnv+"=") {
			continue
		}
		env = append(env, e)
	}
	cmd.Env = append(append(env, skipRTSInitEnv+"=1", loaderScenarioEnv+"="+scenario), extra...)
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("scenario %s failed (%v):\n%s", scenario, err, out)
	}
	return string(out)
}

// Every way a library can fail the binding is refused with an error naming
// the failure, by a backend and by [StartRuntime] alike, and never a panic or
// a silent answer: a library that opens but carries none of the kernel's
// symbols, a file that is not a library, a library laid out for another ABI
// version, one at this version carrying nothing else, and a kernel that
// answers null. The renderer and the decimal parser open no library: with the
// runtime down each refuses on the runtime. The search for the library is
// exercised with no path in the environment. The null-kernel and
// recording-kernel scenarios also read what a stand-in answers, its
// allocation count among it.
func TestLoaderFailuresAreVocal(t *testing.T) {
	if scenario := os.Getenv(loaderScenarioEnv); scenario != "" {
		runLoaderScenario(scenario) // os.Exits; never returns
	}
	lib := findFFILibrary()
	if lib == "" {
		t.Skip("libaletheia-ffi.so not found; run 'cabal run shake -- build' first")
	}
	notALibrary := filepath.Join(t.TempDir(), "not-a-library.so")
	if err := os.WriteFile(notALibrary, []byte("not an ELF object\n"), 0o600); err != nil {
		t.Fatal(err)
	}
	scenarios := map[string]string{
		"symbolless":       standIn(t, lib, "symbolless"),
		"not-a-library":    notALibrary,
		"null-kernel":      standIn(t, lib, "null_kernel"),
		"recording-kernel": standIn(t, lib, "recording_kernel"),
		"stale-abi":        standIn(t, lib, "stale_abi_kernel"),
		"abi-only":         standIn(t, lib, "abi_only_kernel"),
		"search":           "",
	}
	for scenario, lib := range scenarios {
		t.Run(scenario, func(t *testing.T) {
			dir := ""
			if scenario == "search" {
				dir = searchFixture(t)
			}
			out := runLoaderChild(t, scenario, lib, dir)
			if !strings.Contains(out, "LOADER_OK") {
				t.Fatalf("the child did not confirm the scenario:\n%s", out)
			}
		})
	}
}

// searchFixture is a working directory two below a build/ holding the
// library: the layout a checkout gives this package's directory, made for the
// search scenario wherever the package is being tested.
func searchFixture(t *testing.T) string {
	t.Helper()
	lib := findFFILibrary()
	if lib == "" {
		t.Skip("libaletheia-ffi.so not found; run 'cabal run shake -- build' first")
	}
	lib, err := filepath.Abs(lib)
	if err != nil {
		t.Fatal(err)
	}
	root := t.TempDir()
	build := filepath.Join(root, "build")
	dir := filepath.Join(root, "a", "b")
	for _, d := range []string{build, dir} {
		if err := os.MkdirAll(d, 0o755); err != nil {
			t.Fatal(err)
		}
	}
	if err := os.Symlink(lib, filepath.Join(build, "libaletheia-ffi.so")); err != nil {
		t.Fatal(err)
	}
	return dir
}

// runtimeDown is the refusal the renderer and the decimal parser answer while
// the runtime is down, after the words naming what each was doing.
const runtimeDown = "GHC runtime not initialized: call aletheia.StartRuntime or open a client before "

// expect fails the child with a numbered exit when err does not carry the
// text, so the parent's output names which check refused.
func expect(err error, text string, code int) {
	if err == nil || !strings.Contains(err.Error(), text) {
		fmt.Printf("FAIL: got %v, want an error carrying %q\n", err, text)
		os.Exit(code)
	}
}

func expectKind(err error, kind ErrorKind, code int) {
	var e *Error
	if !errors.As(err, &e) || e.Kind != kind {
		fmt.Printf("FAIL: got %v, want an error of kind %v\n", err, kind)
		os.Exit(code)
	}
}

func expectEqual(got, want string, code int) {
	if got != want {
		fmt.Printf("FAIL: got %q, want %q\n", got, want)
		os.Exit(code)
	}
}

// runLoaderScenario is the child's body.
func runLoaderScenario(scenario string) {
	defer func() {
		if r := recover(); r != nil {
			fmt.Printf("FAIL: a consumer panicked instead of refusing: %v\n", r)
			os.Exit(2)
		}
	}()
	lib := os.Getenv("ALETHEIA_LIB")
	half := Rational{Numerator: 1, Denominator: 2}
	switch scenario {
	case "symbolless":
		// The loader resolves the ABI version first and reports it by name;
		// the renderer and the parser, opening nothing, refuse on the runtime.
		_, err := NewFFIBackend(lib)
		expect(err, "dlsym failed for aletheia_abi_version", 10)
		expectKind(err, ErrFFI, 11)
		expect(StartRuntime(lib, 1, nil), "dlsym failed for aletheia_abi_version", 14)
		_, err = formatRational(half)
		expect(err, runtimeDown+"rendering", 12)
		_, err = FromDecimal("0.1")
		expect(err, runtimeDown+"parsing decimals", 13)
	case "stale-abi":
		// A library laid out for another ABI is refused by the version it
		// reports, before any other entry is resolved.
		_, err := NewFFIBackend(lib)
		stale := fmt.Sprintf("the library implements ABI version %d, and this binding needs %d", abiVersion+1, abiVersion)
		expect(err, stale, 15)
		expectKind(err, ErrFFI, 16)
		expect(StartRuntime(lib, 1, nil), stale, 17)
		_, err = FromDecimal("0.1")
		expect(err, runtimeDown+"parsing decimals", 18)
	case "abi-only":
		// A library at this ABI version with nothing else passes the version
		// check, and a backend and a start both refuse at the runtime's start
		// entry, the first they ask for.
		_, err := NewFFIBackend(lib)
		expect(err, "dlsym failed for "+rtsInitSymbol, 40)
		expect(StartRuntime(lib, 1, nil), "dlsym failed for "+rtsInitSymbol, 41)
		if hsInitialized() {
			fmt.Println("FAIL: a refused library started the runtime")
			os.Exit(42)
		}
	case "not-a-library":
		_, err := NewFFIBackend(lib)
		expect(err, "dlopen failed", 20)
		expectKind(err, ErrFFI, 21)
		expect(StartRuntime(lib, 1, nil), "dlopen failed", 22)
	case "null-kernel":
		// The stand-in's runtime entry is a no-op, so the runtime reads as
		// up and every null the stand-in answers reaches the caller as the
		// binding's own refusal of a null. Before it opens, nothing has
		// started the runtime, and the allocation count answers none.
		if allocated, ok := AllocatedBytes(); ok || allocated != 0 {
			fmt.Printf("FAIL: AllocatedBytes answered %d and %v before the runtime started, want no count\n", allocated, ok)
			os.Exit(50)
		}
		b, err := NewFFIBackend(lib)
		if err != nil {
			fmt.Printf("FAIL: the stand-in would not open: %v\n", err)
			os.Exit(30)
		}
		if !hsInitialized() {
			fmt.Println("FAIL: the stand-in's runtime entry did not mark the runtime up")
			os.Exit(31)
		}
		_, err = b.Init()
		expect(err, "aletheia_init returned null", 32)
		_, err = b.Process(0, "{}")
		expect(err, "aletheia_process returned null", 33)
		// The stand-in counts no allocation, and its zero is a count, read
		// through the entry the start recorded.
		if allocated, ok := AllocatedBytes(); !ok || allocated != 0 {
			fmt.Printf("FAIL: AllocatedBytes answered %d and %v, want the stand-in's count of 0\n", allocated, ok)
			os.Exit(51)
		}
		_, err = formatRational(half)
		expect(err, "aletheia_format_rational returned a null pointer", 34)
		_, err = FromDecimal("0.1")
		expect(err, "aletheia_parse_decimal failed without an error", 35)
		expectKind(err, ErrProtocol, 36)
		// With the renderer refusing, the enrichment falls back to the
		// formula alone and the refusal message's rational to a bare form.
		diag := PropertyDiagnostic{Signals: []SignalName{"Speed"}, FormulaDesc: "always(Speed < 220)"}
		values := map[SignalName]Rational{"Speed": half}
		expectEqual(formatObservedBase(diag, values), "violated: always(Speed < 220)", 37)
		expectEqual(formatRationalExact(Rational{Numerator: 3, Denominator: 1}), "3", 38)
		expectEqual(formatRationalExact(Rational{Numerator: 1, Denominator: 3}), "1/3", 39)
	case "recording-kernel":
		// The stand-in answers 2^63 plus the reads made before, so the first
		// two reads of a fresh process set the count's top bit, which a read
		// narrowed below 64 bits or taken as signed reads as another number,
		// and differ by one, which shows that each read reached the entry.
		if _, err := NewFFIBackend(lib); err != nil {
			fmt.Printf("FAIL: the stand-in would not open: %v\n", err)
			os.Exit(52)
		}
		for read, want := range []uint64{1 << 63, 1<<63 + 1} {
			if allocated, ok := AllocatedBytes(); !ok || allocated != want {
				fmt.Printf("FAIL: read %d answered %d and %v, want %d\n", read, allocated, ok, want)
				os.Exit(53 + read)
			}
		}
	case "search":
		// Nothing in the environment: the search answers the build's own
		// locations, relative to the working directory; a directory with
		// none of them yields nothing, as does one the process can no longer
		// name, and the renderer, searching for none, refuses on the runtime.
		here, err := os.Getwd()
		if err != nil {
			fmt.Printf("FAIL: Getwd: %v\n", err)
			os.Exit(40)
		}
		want := filepath.Join(here, "..", "..", "build", "libaletheia-ffi.so")
		expectEqual(findFFILibrary(), want, 41)
		empty, err := os.MkdirTemp("", "aletheia-search")
		if err != nil {
			fmt.Printf("FAIL: MkdirTemp: %v\n", err)
			os.Exit(42)
		}
		if err := os.Chdir(empty); err != nil {
			fmt.Printf("FAIL: Chdir: %v\n", err)
			os.Exit(43)
		}
		expectEqual(findFFILibrary(), "", 44)
		_, err = formatRational(half)
		expect(err, runtimeDown+"rendering", 47)
		if err := os.Remove(empty); err != nil {
			fmt.Printf("FAIL: Remove: %v\n", err)
			os.Exit(45)
		}
		expectEqual(findFFILibrary(), "", 46)
	default:
		fmt.Printf("FAIL: unknown scenario %q\n", scenario)
		os.Exit(1)
	}
	fmt.Println("LOADER_OK")
	os.Exit(0)
}
