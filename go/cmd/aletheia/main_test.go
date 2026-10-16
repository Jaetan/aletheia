// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package main

import (
	"encoding/json"
	"os"
	"path/filepath"
	"regexp"
	"slices"
	"strings"
	"testing"

	"github.com/Jaetan/aletheia/go/excel"
	"github.com/Jaetan/aletheia/go/v5/aletheia"
)

// repoPath joins the test's package dir (go/cmd/aletheia) up to the repo root.
func repoPath(parts ...string) string {
	return filepath.Join(append([]string{"..", "..", ".."}, parts...)...)
}

// ensureLib points the CLI at the built kernel and skips the test when there is
// none, as the binding's other tests do: they run against the real core, never
// a stub.
func ensureLib(t *testing.T) {
	t.Helper()
	if !cgoEnabled {
		t.Skip("built without cgo; the binding cannot load the library")
	}
	if os.Getenv("ALETHEIA_LIB") != "" {
		return
	}
	so := repoPath("build", "libaletheia-ffi.so")
	if _, err := os.Stat(so); err != nil {
		t.Skip("libaletheia-ffi.so not built; run 'cabal run shake -- build'")
	}
	t.Setenv("ALETHEIA_LIB", so)
}

// silenceStdout discards CLI stdout for the duration of a test so subcommand
// output does not clutter `go test -v`.
func silenceStdout(t *testing.T) {
	t.Helper()
	devnull, err := os.OpenFile(os.DevNull, os.O_WRONLY, 0)
	if err != nil {
		t.Fatalf("open %s: %v", os.DevNull, err)
	}
	old := os.Stdout
	os.Stdout = devnull
	t.Cleanup(func() {
		os.Stdout = old
		_ = devnull.Close()
	})
}

// captureStdout runs fn with os.Stdout redirected to a pipe and returns what it
// wrote, so a test can assert the CLI's text output (not just its exit code).
func captureStdout(t *testing.T, fn func()) string {
	t.Helper()
	return capture(t, &os.Stdout, fn)
}

// captureStderr is captureStdout for the error line.
func captureStderr(t *testing.T, fn func()) string {
	t.Helper()
	return capture(t, &os.Stderr, fn)
}

// capture runs fn with *stream redirected to a file and returns what it wrote.
// A file takes any amount of output without a reader beside the writer, which
// a pipe would need.
func capture(t *testing.T, stream **os.File, fn func()) string {
	t.Helper()
	f, err := os.CreateTemp(t.TempDir(), "captured")
	if err != nil {
		t.Fatalf("os.CreateTemp: %v", err)
	}
	old := *stream
	*stream = f
	defer func() { *stream = old }() // restore even if fn panics

	fn()
	if err := f.Close(); err != nil {
		t.Fatalf("closing the capture: %v", err)
	}
	written, err := os.ReadFile(f.Name())
	if err != nil {
		t.Fatalf("reading the capture: %v", err)
	}
	return string(written)
}

// writeFailingDBC writes the minimal fixture with a signal name duplicated,
// which parses and then fails validation, and answers its path.
func writeFailingDBC(t *testing.T) string {
	t.Helper()
	src, err := os.ReadFile(repoPath("python", "tests", "fixtures", "dbc_corpus", "minimal.dbc"))
	if err != nil {
		t.Fatalf("read minimal.dbc fixture: %v", err)
	}
	broken := strings.Replace(string(src), "EngineTemp", "EngineSpeed", 1)
	if broken == string(src) {
		t.Fatal("fixture no longer contains EngineTemp; cannot derive duplicate-signal DBC")
	}
	path := filepath.Join(t.TempDir(), "failing.dbc")
	if err := os.WriteFile(path, []byte(broken), 0o600); err != nil {
		t.Fatalf("write dbc: %v", err)
	}
	return path
}

// TestCLISignalsRendersFactorExactly: a fine-resolution factor (1/8192 =
// 0.0001220703125) renders exactly via the kernel format_rational, never the
// lossy 6-significant-figure %g form ("0.00012207"). example.dbc has no such
// fine factor, so write a dedicated temp DBC, its maximum the most the sixteen
// bits carry, 65535/8192.
func TestCLISignalsRendersFactorExactly(t *testing.T) {
	ensureLib(t)
	dir := t.TempDir()
	dbcPath := filepath.Join(dir, "fine.dbc")
	const dbc = "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_:\n\n" +
		"BO_ 1024 FineMsg: 8 ECU4\n" +
		" SG_ FineSignal : 0|16@1+ (0.0001220703125,0) [0|7.9998779296875] \"x\" Vector__XXX\n"
	if err := os.WriteFile(dbcPath, []byte(dbc), 0o600); err != nil {
		t.Fatalf("write dbc: %v", err)
	}
	out := captureStdout(t, func() {
		if code := run([]string{"signals", "--dbc", dbcPath}); code != exitOK {
			t.Fatalf("signals exit = %d, want %d", code, exitOK)
		}
	})
	if !strings.Contains(out, "x0.0001220703125") {
		t.Errorf("signals output missing the exact factor 0.0001220703125; got:\n%s", out)
	}
}

func TestCLISmoke(t *testing.T) {
	ensureLib(t)
	silenceStdout(t)
	dbc := repoPath("examples", "example.dbc")
	mux := repoPath("python", "tests", "fixtures", "dbc_corpus", "multiplexing.dbc")
	cases := [][]string{
		{"validate", "--dbc", dbc},
		{"validate", "--dbc", dbc, "--json"},
		{"signals", "--dbc", dbc},
		{"signals", "--dbc", dbc, "--json"},
		{"format-dbc", "--dbc", dbc},
		{"extract", "--dbc", dbc, "0x100", "102700000A000000"},
		{"extract", "--dbc", dbc, "0x100", "102700000A000000", "--json"}, // flag after positionals
		{"mux-query", "--dbc", mux, "0x64"},
		{"mux-query", "--dbc", mux, "0x64", "--mux", "Mode", "--value", "1"},
		{"mux-query", "--dbc", mux, "0x64", "--mux", "Mode", "--value", "1", "--json"},
	}
	for _, args := range cases {
		if code := run(args); code != exitOK {
			t.Errorf("run(%v) = %d, want %d", args, code, exitOK)
		}
	}
	// One of the pair without the other is an error, not a query of everything.
	if code := run([]string{"mux-query", "--dbc", mux, "0x64", "--mux", "Mode"}); code != exitError {
		t.Errorf("mux-query --mux without --value = %d, want %d", code, exitError)
	}
}

// TestCLIValidateInvalidDBC: a DBC that parses and then fails validation is
// reported as the numbered issue list, in the shape a passing one is reported
// in, and exits one rather than dying with a bare message and exiting two. The
// DBC is the minimal fixture with a signal name duplicated.
func TestCLIValidateInvalidDBC(t *testing.T) {
	ensureLib(t)
	dbcPath := writeFailingDBC(t)

	t.Run("text lists issues and exits 1", func(t *testing.T) {
		out := captureStdout(t, func() {
			if code := run([]string{"validate", "--dbc", dbcPath}); code != exitViolations {
				t.Errorf("validate exit = %d, want %d", code, exitViolations)
			}
		})
		if !strings.Contains(out, "Validation FAILED") {
			t.Errorf("output missing the FAILED header; got:\n%s", out)
		}
		if !strings.Contains(out, "1. [ERROR] duplicate_signal_name") {
			t.Errorf("output missing the numbered duplicate_signal_name issue; got:\n%s", out)
		}
	})

	t.Run("json emits the has_errors fail shape", func(t *testing.T) {
		var code int
		out := captureStdout(t, func() {
			code = run([]string{"validate", "--dbc", dbcPath, "--json"})
		})
		// The exit code reflects the validation outcome in both output
		// modes: --json on a has_errors result exits 1 like text mode.
		if code != exitViolations {
			t.Errorf("validate --json exit = %d, want %d", code, exitViolations)
		}
		var payload struct {
			Status    string           `json:"status"`
			HasErrors bool             `json:"has_errors"`
			Total     int              `json:"total_issues"`
			Issues    []map[string]any `json:"issues"`
		}
		if err := json.Unmarshal([]byte(out), &payload); err != nil {
			t.Fatalf("output is not valid JSON: %v\n%s", err, out)
		}
		if !strings.HasSuffix(out, "}\n") {
			t.Errorf("the JSON report does not end its last line; got %q", out)
		}
		if payload.Status != "fail" || !payload.HasErrors {
			t.Errorf("status/has_errors = %q/%v, want fail/true", payload.Status, payload.HasErrors)
		}
		if payload.Total != len(payload.Issues) || len(payload.Issues) == 0 {
			t.Fatalf("total_issues = %d with %d issues, want a consistent non-empty list",
				payload.Total, len(payload.Issues))
		}
		found := false
		for _, issue := range payload.Issues {
			if issue["code"] == "duplicate_signal_name" {
				found = true
			}
		}
		if !found {
			t.Errorf("issues missing duplicate_signal_name; got %v", payload.Issues)
		}
	})

	t.Run("unparseable dbc still dies with exit 2", func(t *testing.T) {
		garbagePath := filepath.Join(t.TempDir(), "garbage.dbc")
		if err := os.WriteFile(garbagePath, []byte("this is not a dbc\n"), 0o600); err != nil {
			t.Fatalf("write dbc: %v", err)
		}
		if code := run([]string{"validate", "--dbc", garbagePath}); code != exitError {
			t.Errorf("validate on unparseable dbc = %d, want %d", code, exitError)
		}
	})

	t.Run("other subcommands still die with exit 2", func(t *testing.T) {
		silenceStdout(t)
		if code := run([]string{"signals", "--dbc", dbcPath}); code != exitError {
			t.Errorf("signals on invalid dbc = %d, want %d", code, exitError)
		}
	})
}

// TestCLIValidateWarningsFromSingleParse: validate asks the kernel once, the
// parse epilogue being the whole of validation, so the warnings the parse
// returns are the entire issue list. The minimal fixture parses clean and
// carries one harmless warning, which reaches the passing report without a
// second round trip.
func TestCLIValidateWarningsFromSingleParse(t *testing.T) {
	ensureLib(t)
	dbc := repoPath("python", "tests", "fixtures", "dbc_corpus", "minimal.dbc")
	out := captureStdout(t, func() {
		if code := run([]string{"validate", "--dbc", dbc}); code != exitOK {
			t.Errorf("validate exit = %d, want %d", code, exitOK)
		}
	})
	if !strings.Contains(out, "Validation passed with 1 warnings") {
		t.Errorf("output missing the passed-with-warnings header; got:\n%s", out)
	}
	if !strings.Contains(out, "offset_scale_range") {
		t.Errorf("output missing the offset_scale_range warning carried from the parse; got:\n%s", out)
	}
}

func TestCLICheckDeferred(t *testing.T) {
	// The interface does not carry check, and says so rather than succeeding.
	if code := run([]string{"check"}); code != exitError {
		t.Errorf("run([check]) = %d, want %d", code, exitError)
	}
}

// TestCLITemplateWritesTheWorkbookTheLoadersRead: the file written is the
// workbook the Excel module reads, its sheets present and headed, nothing under
// the headers. Writing it goes through the Excel module, not the core, so the
// test needs no library.
func TestCLITemplateWritesTheWorkbookTheLoadersRead(t *testing.T) {
	path := filepath.Join(t.TempDir(), "checks.xlsx")
	var code int
	out := captureStdout(t, func() { code = run([]string{"template", path}) })
	if code != exitOK {
		t.Fatalf("run([template %s]) = %d, want %d", path, code, exitOK)
	}
	if want := "Template written to " + path + "\n"; out != want {
		t.Errorf("stdout = %q, want %q", out, want)
	}
	checks, err := excel.LoadChecks(path)
	if err != nil {
		t.Fatalf("LoadChecks on the template: %v", err)
	}
	if len(checks) != 0 {
		t.Errorf("LoadChecks on the template = %d checks, want none", len(checks))
	}
	if _, err := excel.LoadDbc(path); err == nil || !strings.Contains(err.Error(), "at least one data row") {
		t.Errorf("LoadDbc on the template: err = %v, want the DBC sheet's empty-rows refusal", err)
	}
}

// TestCLITemplateRefusesAnExistingPath: a path that exists exits 2 naming it,
// and its bytes are not touched.
func TestCLITemplateRefusesAnExistingPath(t *testing.T) {
	path := filepath.Join(t.TempDir(), "checks.xlsx")
	if err := os.WriteFile(path, []byte("not a workbook"), 0o600); err != nil {
		t.Fatal(err)
	}
	var code int
	errOut := captureStderr(t, func() { code = run([]string{"template", path}) })
	if code != exitError {
		t.Errorf("run([template existing]) = %d, want %d", code, exitError)
	}
	if want := "Error: aletheia validation error: file already exists: " + path + "\n"; errOut != want {
		t.Errorf("stderr = %q, want %q", errOut, want)
	}
	got, err := os.ReadFile(path)
	if err != nil || string(got) != "not a workbook" {
		t.Errorf("existing file after refusal = %q (%v), want it unchanged", got, err)
	}
}

// TestCLITemplateOperationalErrors: a missing parent directory, a flag the
// command does not take, and a report that cannot be written each exit 2.
func TestCLITemplateOperationalErrors(t *testing.T) {
	dir := t.TempDir()
	for _, argv := range [][]string{
		{"template", filepath.Join(dir, "missing", "checks.xlsx")},
		{"template", "--json", filepath.Join(dir, "a.xlsx")},
	} {
		var code int
		_ = captureStderr(t, func() { code = run(argv) })
		if code != exitError {
			t.Errorf("run(%q) = %d, want %d", argv, code, exitError)
		}
	}
	if entries, err := os.ReadDir(dir); err != nil || len(entries) != 0 {
		t.Errorf("refused runs left %v (%v) behind, want nothing", entries, err)
	}

	// Standard output opened read-only refuses the report's write.
	readOnly, err := os.Open(os.DevNull)
	if err != nil {
		t.Fatal(err)
	}
	defer readOnly.Close()
	var code int
	_ = captureStderr(t, func() {
		old := os.Stdout
		os.Stdout = readOnly
		defer func() { os.Stdout = old }() // restore even if run panics
		code = run([]string{"template", filepath.Join(dir, "unreported.xlsx")})
	})
	if code != exitError {
		t.Errorf("run([template]) with an unwritable stdout = %d, want %d", code, exitError)
	}
}

func TestCLIUnknownCommand(t *testing.T) {
	if code := run([]string{"bogus"}); code != exitError {
		t.Errorf("run([bogus]) = %d, want %d", code, exitError)
	}
}

func TestReorderArgs(t *testing.T) {
	for _, c := range []struct {
		name      string
		argv      []string
		boolFlags map[string]bool
		want      []string
	}{
		{
			name:      "a flag written after the positionals moves ahead of them",
			argv:      []string{"0x100", "DATA", "--dbc", "f.dbc", "--json"},
			boolFlags: map[string]bool{"json": true},
			want:      []string{"--dbc", "f.dbc", "--json", "0x100", "DATA"},
		},
		{
			name: "a flag carrying its own value keeps it",
			argv: []string{"0x100", "--dbc=f.dbc"},
			want: []string{"--dbc=f.dbc", "0x100"},
		},
		{
			name: "nothing after the escape is read as a flag",
			argv: []string{"--", "--dbc", "0x100"},
			want: []string{"--", "--dbc", "0x100"},
		},
		{
			name: "the escape goes ahead of the positionals written before it",
			argv: []string{"0x100", "--dbc", "f.dbc", "--", "-5"},
			want: []string{"--dbc", "f.dbc", "--", "0x100", "-5"},
		},
		{
			name:      "a lone dash is a positional",
			argv:      []string{"-", "--json"},
			boolFlags: map[string]bool{"json": true},
			want:      []string{"--json", "-"},
		},
	} {
		t.Run(c.name, func(t *testing.T) {
			if got := reorderArgs(c.argv, c.boolFlags); !slices.Equal(got, c.want) {
				t.Errorf("reorderArgs(%v) = %v, want %v", c.argv, got, c.want)
			}
		})
	}
}

// TestCLIFlagOnlyCommandsRefuseAPositional: validate, signals and format-dbc
// take flags and no positional. A flag is read wherever it is written, so one
// after a positional is parsed, even past a flag that takes no value, and every
// positional, before the escape or after it, is named in the refusal, which
// comes before the DBC is read: a DBC that does not exist is refused alike.
func TestCLIFlagOnlyCommandsRefuseAPositional(t *testing.T) {
	dbc := repoPath("examples", "example.dbc")
	missing := filepath.Join(t.TempDir(), "missing.dbc")
	for _, command := range []struct {
		name string
		bare []string // the flags it takes without a value
	}{
		{name: "validate", bare: []string{"--json"}},
		{name: "signals", bare: []string{"--json"}},
		{name: "format-dbc"},
	} {
		cmd := command.name
		t.Run(cmd, func(t *testing.T) {
			for _, c := range []struct {
				argv []string
				want string
			}{
				{argv: []string{cmd, "--dbc", dbc, "stray"}, want: "Error: unrecognized arguments: stray\n"},
				{argv: []string{cmd, "stray", "--dbc", dbc, "other"}, want: "Error: unrecognized arguments: stray other\n"},
				{argv: []string{cmd, "--", "--dbc", dbc}, want: "Error: unrecognized arguments: --dbc " + dbc + "\n"},
				{argv: []string{cmd, "stray", "--dbc", dbc, "--", "other"}, want: "Error: unrecognized arguments: stray other\n"},
				{argv: []string{cmd, "--dbc", missing, "stray"}, want: "Error: unrecognized arguments: stray\n"},
				{
					argv: append(append([]string{cmd, "--dbc", dbc}, command.bare...), "stray", "--bogus"),
					want: "flag provided but not defined: -bogus\n",
				},
			} {
				var code int
				var stdout string
				stderr := captureStderr(t, func() {
					stdout = captureStdout(t, func() { code = run(c.argv) })
				})
				if code != exitError || stdout != "" || !strings.HasPrefix(stderr, c.want) {
					t.Errorf("run(%q) = %d, stdout %q, stderr %q; want %d, no output and stderr opening %q",
						c.argv, code, stdout, stderr, exitError, c.want)
				}
			}
		})
	}
}

// TestCLIFixedCountCommandsRefuseAWrongCount: extract, mux-query and template
// take a fixed count of positionals. Too few are refused with the command's
// own line naming what it takes, and extras, a token after the escape among
// them, are named alone in the words the Python CLI's parser uses. Either
// refusal comes before the DBC is read, so a DBC that does not exist is
// refused alike, and template writes no file.
func TestCLIFixedCountCommandsRefuseAWrongCount(t *testing.T) {
	dir := t.TempDir()
	missing := filepath.Join(dir, "missing.dbc")
	const (
		extractRequires  = "Error: extract requires <can_id> <data> positional arguments\n"
		muxQueryRequires = "Error: mux-query requires a <message> positional argument (CAN ID or name)\n"
		templateRequires = "Error: template requires one <path> positional argument\n"
	)
	for _, c := range []struct {
		argv []string
		want string
	}{
		{argv: []string{"extract", "--dbc", missing}, want: extractRequires},
		{argv: []string{"extract", "--dbc", missing, "0x100"}, want: extractRequires},
		{
			argv: []string{"extract", "--dbc", missing, "0x100", "00", "stray", "other"},
			want: "Error: unrecognized arguments: stray other\n",
		},
		{argv: []string{"mux-query", "--dbc", missing}, want: muxQueryRequires},
		{argv: []string{"mux-query", "--dbc", missing, "0x100", "stray"}, want: "Error: unrecognized arguments: stray\n"},
		{argv: []string{"mux-query", "--dbc", missing, "--", "0x100", "--json"}, want: "Error: unrecognized arguments: --json\n"},
		{argv: []string{"template"}, want: templateRequires},
		{argv: []string{"template", filepath.Join(dir, "a.xlsx"), "stray"}, want: "Error: unrecognized arguments: stray\n"},
		{argv: []string{"template", filepath.Join(dir, "a.xlsx"), "--", "stray"}, want: "Error: unrecognized arguments: stray\n"},
	} {
		var code int
		var stdout string
		stderr := captureStderr(t, func() {
			stdout = captureStdout(t, func() { code = run(c.argv) })
		})
		if code != exitError || stdout != "" || stderr != c.want {
			t.Errorf("run(%q) = %d, stdout %q, stderr %q; want %d, no output and stderr %q",
				c.argv, code, stdout, stderr, exitError, c.want)
		}
	}
	if entries, err := os.ReadDir(dir); err != nil || len(entries) != 0 {
		t.Errorf("refused runs left %v (%v) behind, want nothing", entries, err)
	}
}

// TestCLIMuxQueryTakesTheMessageAfterTheEscape: every token after "--" is a
// positional, so mux-query takes its message there, one that reads as a flag
// included, and looks it up rather than refusing it as a flag.
func TestCLIMuxQueryTakesTheMessageAfterTheEscape(t *testing.T) {
	ensureLib(t)
	dbc := repoPath("python", "tests", "fixtures", "dbc_corpus", "minimal.dbc")
	for _, c := range []struct {
		message, stdout, stderr string
		code                    int
	}{
		{
			message: "0x100",
			stdout:  "Message 0x100 EngineStatus (DLC 8)\n  Not multiplexed: all 3 signals are always present.\n",
			code:    exitOK,
		},
		{message: "-5", stderr: "Error: message not found by id or name: \"-5\"\n", code: exitError},
	} {
		argv := []string{"mux-query", "--dbc", dbc, "--", c.message}
		var code int
		var stdout string
		stderr := captureStderr(t, func() {
			stdout = captureStdout(t, func() { code = run(argv) })
		})
		if code != c.code || stdout != c.stdout || stderr != c.stderr {
			t.Errorf("run(%q) = %d, stdout %q, stderr %q; want %d, stdout %q, stderr %q",
				argv, code, stdout, stderr, c.code, c.stdout, c.stderr)
		}
	}
}

// TestArgumentParsersRefuseWhatTheyCannotRead: the three readers between the
// command line and the kernel, checked without one, since nothing else does.
func TestArgumentParsersRefuseWhatTheyCannotRead(t *testing.T) {
	t.Run("a CAN identifier is decimal or hexadecimal", func(t *testing.T) {
		for _, c := range []struct {
			in      string
			want    uint32
			refused bool
		}{
			{in: "0x100", want: 0x100},
			{in: "0X100", want: 0x100},
			{in: " 256 ", want: 256},
			{in: "256", want: 256},
			{in: "0x1FFFFFFF", want: 0x1FFFFFFF},
			{in: "0x100000000", refused: true},
			{in: "-1", refused: true},
			{in: "", refused: true},
			{in: "0xZZ", refused: true},
		} {
			got, err := parseCANID(c.in)
			if c.refused {
				if err == nil {
					t.Errorf("parseCANID(%q) = %d, want a refusal", c.in, got)
				}
				continue
			}
			if err != nil || got != c.want {
				t.Errorf("parseCANID(%q) = %d, %v, want %d", c.in, got, err, c.want)
			}
		}
	})

	t.Run("frame bytes are hexadecimal, however they are written", func(t *testing.T) {
		for _, c := range []struct {
			in      string
			want    []byte
			refused bool
		}{
			{in: "0A1B", want: []byte{0x0A, 0x1B}},
			{in: "0x0a1b", want: []byte{0x0A, 0x1B}},
			{in: "0A 1B", want: []byte{0x0A, 0x1B}},
			{in: "0A:1B", want: []byte{0x0A, 0x1B}},
			{in: "", want: []byte{}},
			{in: "0A1", refused: true},
			{in: "ZZ", refused: true},
		} {
			got, err := parseHexData(c.in)
			if c.refused {
				if err == nil {
					t.Errorf("parseHexData(%q) = %v, want a refusal", c.in, got)
				}
				continue
			}
			if err != nil || !slices.Equal(got, c.want) {
				t.Errorf("parseHexData(%q) = %v, %v, want %v", c.in, got, err, c.want)
			}
		}
	})

	t.Run("an identifier past eleven bits needs the extended flag", func(t *testing.T) {
		if _, err := makeCANID(0x800, false); err == nil {
			t.Error("makeCANID(0x800, standard) was accepted, want a refusal naming --extended")
		} else if !strings.Contains(err.Error(), "--extended") {
			t.Errorf("the refusal does not name the flag that accepts it: %v", err)
		}
		if _, err := makeCANID(0x800, true); err != nil {
			t.Errorf("makeCANID(0x800, extended) = %v, want it accepted", err)
		}
		if _, err := makeCANID(0x20000000, true); err == nil {
			t.Error("makeCANID past twenty-nine bits was accepted, want a refusal")
		}
	})
}

// TestCLIClosesEveryClientItOpens: a subcommand that returns without closing
// its client leaves behind the handle the binding holds on the Haskell side,
// which the count reports and a long-lived host would accumulate.
func TestCLIClosesEveryClientItOpens(t *testing.T) {
	ensureLib(t)
	silenceStdout(t)
	dbc := repoPath("python", "tests", "fixtures", "dbc_corpus", "minimal.dbc")
	before := aletheia.StablePtrCount()
	for _, argv := range [][]string{
		{"validate", "--dbc", dbc},
		{"signals", "--dbc", dbc},
		{"format-dbc", "--dbc", dbc},
		{"extract", "--dbc", dbc, "0x100", "0000000000000000"},
		{"mux-query", "--dbc", dbc, "0x100"},
	} {
		run(argv)
		if held := aletheia.StablePtrCount(); held != before {
			t.Errorf("after %v the binding holds %d handles, want %d", argv, held, before)
		}
	}
}

// textReport is one text report and the whole of what it prints.
type textReport struct {
	argv []string
	want string
}

// textReports reaches every part of every text report: validate passing
// clean, passing with a warning and failing; signals; extract with a unit, an
// absent signal, an extraction error and no value at all; mux-query on a plain
// message, on a multiplexed one and on one multiplexor value.
func textReports(t *testing.T) []textReport {
	t.Helper()
	dbc := repoPath("python", "tests", "fixtures", "dbc_corpus", "minimal.dbc")
	mux := repoPath("python", "tests", "fixtures", "dbc_corpus", "multiplexing.dbc")
	// One signal whose bits carry more than its declared maximum, so a frame
	// of all ones extracts no value and one error.
	bounded := filepath.Join(t.TempDir(), "bounded.dbc")
	const boundedDBC = "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_:\n\n" +
		"BO_ 1024 Bounded: 2 ECU\n" +
		" SG_ Speed : 0|16@1+ (0.25,0) [0|8000] \"rpm\" Vector__XXX\n"
	if err := os.WriteFile(bounded, []byte(boundedDBC), 0o600); err != nil {
		t.Fatalf("write dbc: %v", err)
	}
	const rangeWarning = "offset_scale_range: Message 'EngineStatus', signal 'EngineSpeed': " +
		"its bits carry values above the declared maximum\n"
	return []textReport{
		{[]string{"validate", "--dbc", mux}, "Validation passed: no issues found\n"},
		{[]string{"validate", "--dbc", dbc}, "Validation passed with 1 warnings\n\n" +
			"  1. [WARNING] " + rangeWarning},
		{[]string{"validate", "--dbc", writeFailingDBC(t)}, "Validation FAILED (2 issues)\n\n" +
			"  1. [ERROR] duplicate_signal_name: Message 'EngineStatus': duplicate signal name 'EngineSpeed'\n" +
			"  2. [WARNING] " + rangeWarning},
		{[]string{"signals", "--dbc", dbc}, "Message 0x100 EngineStatus (DLC 8)\n" +
			"  EngineSpeed          bits[0:16] LE unsigned x0.25 +0 rpm\n" +
			"  EngineTemp           bits[16:8] LE unsigned x1 -40 degC\n" +
			"  CoolantLevel         bits[24:8] LE unsigned x1 +0 \n" +
			"Message 0x200 BrakeStatus (DLC 4)\n" +
			"  BrakePressure        bits[7:16] BE unsigned x0.1 +0 bar\n" +
			"  BrakePedalPct        bits[23:8] BE signed   x0.5 +0 %\n" +
			"  BrakeWarning         bits[31:1] BE unsigned x1 +0 \n" +
			"\n2 messages, 6 signals\n"},
		{[]string{"extract", "--dbc", mux, "0x64", "0100000000000000"}, "CAN ID 0x64 (BasicMux):\n\n" +
			"  Mode                 = 1\n" +
			"  PayloadB             = 0 V\n" +
			"  CommonCounter        = 0\n" +
			"Absent: PayloadA, PayloadC\n"},
		{[]string{"extract", "--dbc", bounded, "0x400", "FFFF"}, "CAN ID 0x400 (Bounded):\n\n" +
			"  (no signals)\n" +
			"\nErrors:\n" +
			"  Speed: value out of bounds: 16383.75 not in [0, 8000]\n"},
		{[]string{"mux-query", "--dbc", dbc, "0x100"}, "Message 0x100 EngineStatus (DLC 8)\n" +
			"  Not multiplexed: all 3 signals are always present.\n"},
		{[]string{"mux-query", "--dbc", mux, "0x64"}, "Message 0x64 BasicMux (DLC 8)\n" +
			"  Mode:\n" +
			"    value 0: 3 signals (Mode, PayloadA, CommonCounter)\n" +
			"    value 1: 3 signals (Mode, PayloadB, CommonCounter)\n" +
			"    value 2: 3 signals (Mode, PayloadC, CommonCounter)\n"},
		{[]string{"mux-query", "--dbc", mux, "0x64", "--mux", "Mode", "--value", "1"}, "Message 0x64 BasicMux (DLC 8)\n" +
			"Multiplexor Mode = 1: 3 signals present\n" +
			"  Mode\n" +
			"  PayloadB\n" +
			"  CommonCounter\n"},
	}
}

// TestCLITextReports: each text report prints exactly its lines, in order.
func TestCLITextReports(t *testing.T) {
	ensureLib(t)
	for _, r := range textReports(t) {
		if got := captureStdout(t, func() { run(r.argv) }); got != r.want {
			t.Errorf("run(%v) printed:\n%s\nwant:\n%s", r.argv, got, r.want)
		}
	}
}

// TestCLIReportThatCannotBeWrittenIsAnError: a subcommand whose report, JSON
// or text, or the template's confirmation line, cannot be written exits with
// the error code and says so, since a caller redirecting the stream into a file
// would otherwise read a truncated report from a run that succeeded, or a
// validation outcome with no report beside it. Each report reaches the writer
// by its own path, so each is run, stdout being /dev/full, which takes an open
// and refuses every write.
func TestCLIReportThatCannotBeWrittenIsAnError(t *testing.T) {
	ensureLib(t)
	dbc := repoPath("python", "tests", "fixtures", "dbc_corpus", "minimal.dbc")
	mux := repoPath("python", "tests", "fixtures", "dbc_corpus", "multiplexing.dbc")
	argvs := [][]string{
		{"validate", "--dbc", dbc, "--json"},
		{"validate", "--dbc", writeFailingDBC(t), "--json"},
		{"signals", "--dbc", dbc, "--json"},
		{"format-dbc", "--dbc", dbc},
		{"extract", "--dbc", dbc, "0x100", "0000000000000000", "--json"},
		{"mux-query", "--dbc", mux, "0x64", "--json"},
		{"mux-query", "--dbc", mux, "0x64", "--mux", "Mode", "--value", "1", "--json"},
		{"template", filepath.Join(t.TempDir(), "template.xlsx")},
	}
	for _, r := range textReports(t) {
		argvs = append(argvs, r.argv)
	}
	for _, argv := range argvs {
		var code int
		stderr := captureStderr(t, func() {
			withStdout(t, "/dev/full", func() { code = run(argv) })
		})
		if want := "Error: writing the report: No space left on device\n"; code != exitError || stderr != want {
			t.Errorf("run(%v) with nowhere to write = %d, stderr %q; want %d and %q",
				argv, code, stderr, exitError, want)
		}
	}
}

// withStdout runs fn with os.Stdout opened on path for writing.
func withStdout(t *testing.T, path string, fn func()) {
	t.Helper()
	f, err := os.OpenFile(path, os.O_WRONLY, 0)
	if err != nil {
		t.Fatalf("open %s: %v", path, err)
	}
	defer func() { _ = f.Close() }()
	old := os.Stdout
	os.Stdout = f
	defer func() { os.Stdout = old }()
	fn()
}

// TestGuideShellLinesRunAsWritten: the shell line docs/reference/GO_API.md
// prints, and the one docs/reference/CLI.md prints, each run from go/, the
// directory both guides name, with ALETHEIA_LIB unset or empty, and list the
// messages of the DBC they name. No harness runs a shell fence, so each line is
// read out of its guide and a guide changed without running it fails here. A
// line is data, split on spaces and never handed to a shell, so a character a
// shell would read otherwise is refused.
func TestGuideShellLinesRunAsWritten(t *testing.T) {
	if !cgoEnabled {
		t.Skip("built without cgo; the binding cannot load the library")
	}
	// Absolute, since the test changes directory before it runs the line.
	goDir, err := filepath.Abs(repoPath("go"))
	if err != nil {
		t.Fatalf("filepath.Abs: %v", err)
	}
	if _, err := os.Stat(filepath.Join(goDir, "..", "build", "libaletheia-ffi.so")); err != nil {
		t.Skip("libaletheia-ffi.so not built; run 'cabal run shake -- build'")
	}
	const prefix = "go run ./cmd/aletheia "
	for _, name := range []string{"GO_API.md", "CLI.md"} {
		t.Run(name, func(t *testing.T) {
			guide, err := os.ReadFile(repoPath("docs", "reference", name))
			if err != nil {
				t.Fatalf("reading the guide: %v", err)
			}
			line := regexp.MustCompile(`(?m)^` + regexp.QuoteMeta(prefix) + `.*$`).Find(guide)
			if line == nil {
				t.Fatalf("the guide no longer prints a line starting with %q", prefix)
			}
			if !regexp.MustCompile(`^[A-Za-z0-9./_ -]+$`).Match(line) {
				t.Fatalf("the guide's line %q carries a character a shell reads, which this test does not run", line)
			}
			fields := strings.Fields(string(line))
			here, err := os.Stat(".")
			if err != nil {
				t.Fatalf("os.Stat: %v", err)
			}
			if pkg, err := os.Stat(filepath.Join(goDir, fields[2])); err != nil || !os.SameFile(pkg, here) {
				t.Fatalf("from go/, %s is not this package", fields[2])
			}

			t.Chdir(goDir)
			for _, unset := range []bool{true, false} {
				t.Setenv("ALETHEIA_LIB", "")
				if unset {
					if err := os.Unsetenv("ALETHEIA_LIB"); err != nil {
						t.Fatalf("os.Unsetenv: %v", err)
					}
				}
				var code int
				out := captureStdout(t, func() { code = run(fields[3:]) })
				if code != exitOK {
					t.Fatalf("the guide's line %q exits %d from go/, ALETHEIA_LIB unset %v; want %d",
						line, code, unset, exitOK)
				}
				if !regexp.MustCompile(`(?m)^Message `).MatchString(out) {
					t.Errorf("the guide's line ran and listed no message, ALETHEIA_LIB unset %v:\n%s", unset, out)
				}
			}
		})
	}
}

// plant writes an empty file at path, making its directories, for a test that
// asks resolveLib to find it.
func plant(t *testing.T, path string) os.FileInfo {
	t.Helper()
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		t.Fatalf("os.MkdirAll: %v", err)
	}
	if err := os.WriteFile(path, nil, 0o644); err != nil {
		t.Fatalf("os.WriteFile: %v", err)
	}
	fi, err := os.Stat(path)
	if err != nil {
		t.Fatalf("os.Stat: %v", err)
	}
	return fi
}

// deepEmptyDir makes an empty directory nested deep enough that every relative
// directory resolveLib searches from it lies inside the test's own temporary
// tree.
func deepEmptyDir(t *testing.T) string {
	t.Helper()
	dir := filepath.Join(t.TempDir(), "a", "b", "c")
	if err := os.MkdirAll(dir, 0o755); err != nil {
		t.Fatalf("os.MkdirAll: %v", err)
	}
	return dir
}

// TestResolveLibFindsTheBuildTree: from each directory the CLI runs from, the
// repository root, go/ and go/cmd/aletheia, resolveLib finds the root's
// build/libaletheia-ffi.so in a planted tree, ALETHEIA_LIB empty and no system
// library in reach.
func TestResolveLibFindsTheBuildTree(t *testing.T) {
	root := t.TempDir()
	want := plant(t, filepath.Join(root, "build", "libaletheia-ffi.so"))
	sysRoot := t.TempDir()
	for _, dir := range []string{".", "go", filepath.Join("go", "cmd", "aletheia")} {
		t.Run(dir, func(t *testing.T) {
			wd := filepath.Join(root, dir)
			if err := os.MkdirAll(wd, 0o755); err != nil {
				t.Fatalf("os.MkdirAll: %v", err)
			}
			t.Chdir(wd)
			t.Setenv("ALETHEIA_LIB", "")
			got := resolveLib(sysRoot)
			if fi, err := os.Stat(got); err != nil || !os.SameFile(fi, want) {
				t.Errorf("from %s, resolveLib = %q; want the root's build/libaletheia-ffi.so", dir, got)
			}
		})
	}
}

// TestResolveLibFallsBackToTheSystemDirectory: with no build tree in reach,
// resolveLib finds usr/local/lib/libaletheia-ffi.so under the system root it is
// given.
func TestResolveLibFallsBackToTheSystemDirectory(t *testing.T) {
	sysRoot := t.TempDir()
	so := filepath.Join(sysRoot, "usr", "local", "lib", "libaletheia-ffi.so")
	plant(t, so)
	t.Chdir(deepEmptyDir(t))
	t.Setenv("ALETHEIA_LIB", "")
	if got := resolveLib(sysRoot); got != so {
		t.Errorf("resolveLib = %q; want %q", got, so)
	}
}

// TestResolveLibTakesTheEnvironmentFirst: a set ALETHEIA_LIB is the answer as
// given, unchecked, ahead of a build tree in reach.
func TestResolveLibTakesTheEnvironmentFirst(t *testing.T) {
	root := t.TempDir()
	plant(t, filepath.Join(root, "build", "libaletheia-ffi.so"))
	t.Chdir(root)
	const env = "/nonexistent/libaletheia-ffi.so"
	t.Setenv("ALETHEIA_LIB", env)
	if got := resolveLib(t.TempDir()); got != env {
		t.Errorf("resolveLib = %q; want %q", got, env)
	}
}

// TestResolveLibAnswersNothingOutOfReach: with no library in reach, resolveLib
// answers the empty path.
func TestResolveLibAnswersNothingOutOfReach(t *testing.T) {
	t.Chdir(deepEmptyDir(t))
	t.Setenv("ALETHEIA_LIB", "")
	if got := resolveLib(t.TempDir()); got != "" {
		t.Errorf("resolveLib = %q; want none", got)
	}
}

// TestNewClientNotFound: with no library in reach, newClient's error is the
// line the C++ CLI prints. The system directory is searched from the root, not
// from the working directory, so a library under the working directory's
// usr/local/lib is not taken. A machine with the library installed in
// /usr/local/lib answers from it, so the test skips on one.
func TestNewClientNotFound(t *testing.T) {
	if _, err := os.Stat("/usr/local/lib/libaletheia-ffi.so"); err == nil {
		t.Skip("libaletheia-ffi.so is installed in /usr/local/lib")
	}
	wd := deepEmptyDir(t)
	plant(t, filepath.Join(wd, "usr", "local", "lib", "libaletheia-ffi.so"))
	t.Chdir(wd)
	t.Setenv("ALETHEIA_LIB", "")
	const want = "libaletheia-ffi.so not found; set $ALETHEIA_LIB or run 'cabal run shake -- build'"
	if _, err := newClient(); err == nil || err.Error() != want {
		t.Errorf("newClient error = %v; want %q", err, want)
	}
}
