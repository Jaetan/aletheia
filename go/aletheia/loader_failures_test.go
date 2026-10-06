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
// opens a library the parent cannot: the library is opened once per process,
// the renderer and the decimal parser resolve their symbols once, and the
// registered default path is written once, so the state each scenario reads
// exists only in a fresh process.
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
	exe, err := os.Executable()
	if err != nil {
		t.Fatalf("the test binary's own path: %v", err)
	}
	cmd := exec.Command(exe, "-test.run=^TestLoaderFailuresAreVocal$", "-test.v")
	cmd.Dir = dir
	env := make([]string, 0, len(os.Environ())+3)
	for _, e := range os.Environ() {
		if strings.HasPrefix(e, "ALETHEIA_LIB=") || strings.HasPrefix(e, skipRTSInitEnv+"=") || strings.HasPrefix(e, loaderScenarioEnv+"=") {
			continue
		}
		env = append(env, e)
	}
	env = append(env, skipRTSInitEnv+"=1", loaderScenarioEnv+"="+scenario)
	if lib != "" {
		env = append(env, "ALETHEIA_LIB="+lib)
	}
	cmd.Env = env
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("scenario %s failed (%v):\n%s", scenario, err, out)
	}
	return string(out)
}

// Every way a library can fail the binding is refused with an error naming
// the failure, and never a panic or a silent answer: a library that opens but
// carries none of the kernel's symbols, a file that is not a library, and a
// kernel that answers null. The search for the library is exercised the same
// way, with no path in the environment.
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
		"symbolless":    standIn(t, lib, "symbolless"),
		"not-a-library": notALibrary,
		"null-kernel":   standIn(t, lib, "null_kernel"),
		"stale-abi":     standIn(t, lib, "stale_abi_kernel"),
		"abi-only":      standIn(t, lib, "abi_only_kernel"),
		"search":        "",
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
		// The backend resolves the ABI version first and reports it by
		// name; the renderer and the parser each ask for their own.
		_, err := NewFFIBackend(lib)
		expect(err, "dlsym failed for aletheia_abi_version", 10)
		expectKind(err, ErrFFI, 11)
		_, err = formatRational(half)
		expect(err, "renderer dlsym aletheia_abi_version", 12)
		_, err = FromDecimal("0.1")
		expect(err, "decimal dlsym aletheia_abi_version", 13)
	case "stale-abi":
		// A library laid out for another ABI is refused by the version it
		// reports, before any other entry is resolved.
		_, err := NewFFIBackend(lib)
		stale := fmt.Sprintf("the library implements ABI version %d, and this binding needs %d", abiVersion+1, abiVersion)
		expect(err, stale, 15)
		expectKind(err, ErrFFI, 16)
		_, err = formatRational(half)
		expect(err, stale, 17)
		_, err = FromDecimal("0.1")
		expect(err, stale, 18)
	case "abi-only":
		// A library at this ABI version with nothing else passes the version
		// check, and each consumer refuses at the first entry it asks for.
		_, err := NewFFIBackend(lib)
		expect(err, "dlsym failed for "+rtsInitSymbol, 40)
		_, err = formatRational(half)
		expect(err, "renderer dlsym aletheia_format_rational", 41)
		_, err = FromDecimal("0.1")
		expect(err, "decimal dlsym aletheia_parse_decimal", 42)
	case "not-a-library":
		_, err := NewFFIBackend(lib)
		expect(err, "dlopen failed", 20)
		expectKind(err, ErrFFI, 21)
		_, err = formatRational(half)
		expect(err, "renderer dlopen failed", 22)
	case "null-kernel":
		// The stand-in's runtime entry is a no-op, so the runtime reads as
		// up and every null the stand-in answers reaches the caller as the
		// binding's own refusal of a null.
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
		_, err = b.Process(nil, "{}")
		expect(err, "aletheia_process returned null", 33)
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
	case "search":
		// Nothing in the environment: a registered path that is gone is
		// passed over for the build's own locations, relative to the
		// working directory; a directory with none of them yields nothing,
		// which the renderer reports as the library not found, as does one
		// the process can no longer name.
		RegisterDefaultLibPath("/nonexistent/libaletheia-ffi.so")
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
		expect(err, "libaletheia-ffi.so not found", 47)
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

// A path a backend registered is what the search answers when the
// environment names none, and a path in the environment that does not exist
// is passed over for it. TestMain's backend, the first opened, registered the
// path the search found, and a later registration does not replace it.
func TestFindFFILibrary_AnswersTheRegisteredPath(t *testing.T) {
	lib := findFFILibrary()
	if lib == "" {
		t.Skip("libaletheia-ffi.so not found; run 'cabal run shake -- build' first")
	}
	RegisterDefaultLibPath("/elsewhere/libaletheia-ffi.so")
	defaultLibPathMu.Lock()
	registered := defaultLibPath
	defaultLibPathMu.Unlock()
	if want := filepath.Clean(lib); registered != want {
		t.Fatalf("registered %q, want %q, the path TestMain's backend opened first", registered, want)
	}
	t.Setenv("ALETHEIA_LIB", "")
	if got := findFFILibrary(); got != registered {
		t.Errorf("with no path in the environment: got %q, want the registered %q", got, registered)
	}
	t.Setenv("ALETHEIA_LIB", "/nonexistent/libaletheia-ffi.so")
	if got := findFFILibrary(); got != registered {
		t.Errorf("with a missing path in the environment: got %q, want the registered %q", got, registered)
	}
}
