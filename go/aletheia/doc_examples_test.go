// Package aletheia_test — Track D.2 doc-example harness.
//
// Mirror of R17 C6 Python `pytest --markdown-docs`: every ```go fence in the
// tracked user-facing markdown files is extracted, wrapped, compiled, and
// executed end-to-end via `go run`. A failing fence (compile or runtime) is
// a test failure with file:line precision. Coverage contract is parity with
// the Python harness — what runs in Python's conftest.py runs here.
//
// Tracked-file list mirrors python/tests/test_doc_examples_harness.py for
// the subset that ships ```go fences. Adding a user-facing markdown file
// means adding it here.
//
// Path substitutions
//
//	"/opt/aletheia/lib/libaletheia-ffi.so" → resolved libaletheia-ffi.so
//	"checks.yaml"                          → testdata/doc_examples/checks.yaml
//	"checks.xlsx" / "tests.xlsx"           → examples/demo/demo_workbook.xlsx
//
// Wrapper shapes
//
//	A. Fence already declares `package main` → used verbatim (after path subst)
//	B. Fence has `import (...)` block but no package decl → prepend `package main`,
//	   append a stub `func main() {}` (Go allows unused top-level funcs)
//	C. Body fragment → wrap inside a synthesized `package main`/`func main()`
//	   with predeclared globals (ctx, client, dbc, ts, canID, dlc, data, frames,
//	   libPath, slog imports) and auto-suppress unused-var errors via go/parser
//	   walk over `:=` declarations.
//
// Companion structural gate: TestNoNotestGoFences rejects `<!-- go notest -->`
// annotations — the only escape hatch is changing the info string to `text`,
// matching the Python `python notest` ban.
package aletheia_test

import (
	"bufio"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strconv"
	"strings"
	"testing"
)

// docFiles lists every user-facing markdown file whose ```go fences run
// under the harness. Keep in sync with the Python equivalent in
// python/tests/test_doc_examples_harness.py and the Go verification block
// in AGENTS.md § Go Verification.
var docFiles = []string{
	"../../README.md",
	"../../docs/PITCH.md",
	"../../docs/architecture/CANCELLATION.md",
	"../../docs/reference/INTERFACES.md",
	"../../docs/development/DISTRIBUTION.md",
}

// Fence is one ```go fenced block.
type goFence struct {
	file    string // repo-relative path
	line    int    // 1-based line number of the opening ```go
	content string // body between fences (no surrounding ``` lines)
}

func (f goFence) name() string {
	// Strip the `../../` prefix used by docFiles for nicer subtest names.
	name := strings.TrimPrefix(f.file, "../../")
	return fmt.Sprintf("%s:L%d", name, f.line)
}

// extractGoFences parses one markdown file and returns every ```go fence.
func extractGoFences(t *testing.T, file string) []goFence {
	t.Helper()
	data, err := os.ReadFile(file)
	if err != nil {
		t.Fatalf("read %s: %v", file, err)
	}
	var fences []goFence
	scanner := bufio.NewScanner(strings.NewReader(string(data)))
	scanner.Buffer(make([]byte, 1024*1024), 1024*1024)
	var (
		inFence    bool
		fenceStart int
		fenceBody  strings.Builder
		lineno     int
	)
	for scanner.Scan() {
		lineno++
		line := scanner.Text()
		trim := strings.TrimLeft(line, " \t")
		if !inFence {
			// Match opening fence: ```go (info string starts with go, not gosomething).
			if strings.HasPrefix(trim, "```go") {
				rest := strings.TrimPrefix(trim, "```go")
				if rest == "" || rest[0] == ' ' || rest[0] == '\t' {
					inFence = true
					fenceStart = lineno
					fenceBody.Reset()
				}
			}
			continue
		}
		// Inside fence — closing line is exactly ``` (possibly indented).
		if strings.TrimSpace(line) == "```" {
			fences = append(fences, goFence{
				file:    file,
				line:    fenceStart,
				content: fenceBody.String(),
			})
			inFence = false
			continue
		}
		fenceBody.WriteString(line)
		fenceBody.WriteByte('\n')
	}
	if err := scanner.Err(); err != nil {
		t.Fatalf("scan %s: %v", file, err)
	}
	if inFence {
		t.Fatalf("%s: unterminated ```go fence opened at line %d", file, fenceStart)
	}
	return fences
}

// findFFILibForDocs locates libaletheia-ffi.so. Mirrors findFFILib from
// ffi_backend_test.go but lives in the *_test package; copied verbatim
// rather than refactored to keep the doc-harness self-contained for
// AGENTS.md cross-reference.
func findFFILibForDocs() string {
	if env := os.Getenv("ALETHEIA_LIB"); env != "" {
		if _, err := os.Stat(env); err == nil {
			return env
		}
	}
	for _, c := range []string{
		"../../build/libaletheia-ffi.so",
		"../build/libaletheia-ffi.so",
		"build/libaletheia-ffi.so",
	} {
		abs, err := filepath.Abs(c)
		if err != nil {
			continue
		}
		if _, err := os.Stat(abs); err == nil {
			return abs
		}
	}
	return ""
}

// repoRootGoDir returns the absolute path to /repo/go (i.e. the parent of
// /repo/go/aletheia, where the test runs). Used by the synthesized go.mod's
// `replace` directive.
func repoRootGoDir(t *testing.T) string {
	t.Helper()
	abs, err := filepath.Abs("..")
	if err != nil {
		t.Fatalf("abs ..: %v", err)
	}
	return abs
}

// substitutePaths rewrites three classes of doc-string paths so the fence
// resolves to fixtures present at test time:
//   - The hardcoded `/opt/aletheia/lib/libaletheia-ffi.so` from
//     DISTRIBUTION.md is rewritten to the resolved libaletheia-ffi.so path.
//   - `checks.yaml` is rewritten to testdata/doc_examples/checks.yaml.
//   - `checks.xlsx` and `tests.xlsx` are rewritten to the existing
//     examples/demo/demo_workbook.xlsx.
//
// Mirrors the function-replacement strategy in python/tests/conftest.py
// (`_harness_dbc_to_json` etc.) but at the source-string level since Go
// doesn't allow runtime function reassignment.
func substitutePaths(body, libPath, yamlFix, excelFix string) string {
	body = strings.ReplaceAll(body, `"/opt/aletheia/lib/libaletheia-ffi.so"`, strconv.Quote(libPath))
	body = strings.ReplaceAll(body, `"checks.yaml"`, strconv.Quote(yamlFix))
	body = strings.ReplaceAll(body, `"checks.xlsx"`, strconv.Quote(excelFix))
	body = strings.ReplaceAll(body, `"tests.xlsx"`, strconv.Quote(excelFix))
	return body
}

// wrapFence picks one of three wrapper shapes based on the fence content.
// Returns the synthesized Go source ready to be written as `main.go`.
//
// Shape A is detected by any line that starts with `package ` after leading
// whitespace — `// comment` blocks may precede the `package` keyword (Go
// allows this; only the first non-comment token must be `package`), so a
// HasPrefix check on the whole trimmed body would miss DISTRIBUTION.md L225.
func wrapFence(body string) string {
	if hasPackageDecl(body) {
		return body
	}
	if hasImportBlock(body) {
		return "package main\n\n" + body + "\nfunc main() {}\n"
	}
	return wrapBodyFragment(body)
}

func hasPackageDecl(body string) bool {
	for _, line := range strings.Split(body, "\n") {
		t := strings.TrimSpace(line)
		if t == "" || strings.HasPrefix(t, "//") || strings.HasPrefix(t, "/*") {
			continue
		}
		return strings.HasPrefix(t, "package ")
	}
	return false
}

func hasImportBlock(body string) bool {
	for _, line := range strings.Split(body, "\n") {
		t := strings.TrimSpace(line)
		if t == "" || strings.HasPrefix(t, "//") {
			continue
		}
		if strings.HasPrefix(t, "import ") || t == "import (" {
			return true
		}
		// A non-comment, non-import statement before any import → not Shape B.
		return false
	}
	return false
}

// wrapBodyFragment synthesizes a full `package main` around a fence whose
// content is just statements/expressions. Predeclared globals match the
// Python harness's `_make_globals` dict; trailing `_ = name` suppressors are
// auto-generated for every `:=` declaration in the fence body via go/parser.
func wrapBodyFragment(body string) string {
	suppressors := unusedSuppressors(body)
	const tmpl = `package main

import (
	"context"
	"errors"
	"fmt"
	"log/slog"
	"os"
	"time"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
	"github.com/aletheia-automotive/aletheia-go/excel"
)

// Force-use of imports the fence may not reference.
var (
	_ = context.Background
	_ = errors.New
	_ = fmt.Sprintf
	_ = slog.Default
	_ = os.Getenv
	_ = time.Now
	_ = aletheia.NewClient
	_ = excel.LoadChecks
)

func buildDocDBC() aletheia.DbcDefinition {
	rat := func(n, d int64) aletheia.Rational { return aletheia.Rational{Numerator: n, Denominator: d} }
	signal := func(name aletheia.SignalName, start aletheia.BitPosition, length aletheia.BitLength, maxVal int64) aletheia.DbcSignal {
		return aletheia.DbcSignal{
			Name:      name,
			StartBit:  start,
			BitLength: length,
			ByteOrder: aletheia.LittleEndian,
			IsSigned:  false,
			Factor:    rat(1, 1),
			Offset:    rat(0, 1),
			Minimum:   rat(0, 1),
			Maximum:   rat(maxVal, 1),
			Unit:      "",
			Presence:  aletheia.AlwaysPresent{},
		}
	}
	sid, _ := aletheia.NewStandardID(0x100)
	dlc, _ := aletheia.NewDLC(8)
	// Two messages: 0x100 ("VehicleState") packs Speed/BrakePedal/EngineRPM
	// for the streaming fences; 0x110 ("Voltages") carries Voltage and
	// BatteryVoltage at start_bit 0 so each YAML check fence resolves
	// against a real signal definition.
	sid2, _ := aletheia.NewStandardID(0x110)
	return aletheia.DbcDefinition{
		Version: "1.0",
		Messages: []aletheia.DbcMessage{
			{
				ID:     sid,
				Name:   "VehicleState",
				DLC:    dlc,
				Sender: "ECU",
				Signals: []aletheia.DbcSignal{
					signal("VehicleSpeed", 0, 16, 65535),
					signal("Speed", 16, 16, 65535),
					signal("BrakePedal", 32, 8, 255),
					signal("EngineRPM", 40, 8, 255),
					signal("FaultCode", 48, 8, 255),
					signal("ParkingBrake", 56, 1, 1),
				},
			},
			{
				ID:     sid2,
				Name:   "Voltages",
				DLC:    dlc,
				Sender: "BMS",
				Signals: []aletheia.DbcSignal{
					signal("Voltage", 0, 16, 65535),
					signal("BatteryVoltage", 16, 16, 65535),
					signal("CoolantTemp", 32, 8, 255),
				},
			},
		},
	}
}

func main() {
	ctx := context.Background()
	libPath := os.Getenv("ALETHEIA_LIB")
	backend, err := aletheia.NewFFIBackend(libPath, aletheia.WithFFILogger(slog.Default()))
	if err != nil {
		panic(err)
	}
	client, err := aletheia.NewClient(backend, aletheia.WithLogger(slog.Default()))
	if err != nil {
		panic(err)
	}
	defer func() { _ = client.Close() }()

	dbcDef := buildDocDBC()
	parsed, err := client.ParseDBC(ctx, dbcDef)
	if err != nil {
		panic(err)
	}
	_ = parsed

	var ts aletheia.Timestamp
	canID, _ := aletheia.NewStandardID(0x100)
	dlc, _ := aletheia.NewDLC(8)
	data := aletheia.FramePayload(make([]byte, 8))
	frames := []aletheia.Frame{}
	dbc := dbcDef
	_, _, _, _, _, _ = ts, canID, dlc, data, frames, dbc

	// Fence body runs in a nested block so fences that redeclare backend /
	// client / ts / canID / dlc / data via short-decl shadow the outer
	// scope's names cleanly. Without the block, a redeclaration in the
	// fence body would fail with "no new variables on left side of :=".
	{
		// ====== FENCE BODY START ======
%s
		// ====== FENCE BODY END ======
%s
	}
	// Outer scope: silence the wrapper's predeclared FFI handles in case
	// no fence reaches them.
	_ = ctx
	_ = backend
	_ = client
}
`
	return fmt.Sprintf(tmpl, body, suppressors)
}

// unusedSuppressors walks `:=` declarations in the fence body and emits
// `_ = name` lines so unused-variable compilation errors don't reject the
// fence. A doc fence may declare `checks, err := ...` and never use either;
// the Python harness ignores this naturally because Python tolerates unused
// names. Go does not, so we add explicit suppressors.
//
// Falls back to "" on parse error — go run will surface the underlying
// error with line:col precision, which is more useful than a synthesized
// suppressor list anyway.
func unusedSuppressors(body string) string {
	src := "package x\nfunc f() {\n" + body + "\n}\n"
	fset := token.NewFileSet()
	file, err := parser.ParseFile(fset, "", src, 0)
	if err != nil {
		return ""
	}
	if len(file.Decls) == 0 {
		return ""
	}
	fn, ok := file.Decls[0].(*ast.FuncDecl)
	if !ok || fn.Body == nil {
		return ""
	}
	var names []string
	seen := map[string]bool{}
	// Only walk top-level statements: a `:=` inside an if / for / switch block
	// scopes its names to that inner block, so a function-scope `_ = name`
	// suppressor wouldn't reach them anyway.
	for _, stmt := range fn.Body.List {
		as, ok := stmt.(*ast.AssignStmt)
		if !ok || as.Tok != token.DEFINE {
			continue
		}
		for _, lhs := range as.Lhs {
			id, ok := lhs.(*ast.Ident)
			if !ok || id.Name == "_" || seen[id.Name] {
				continue
			}
			seen[id.Name] = true
			names = append(names, id.Name)
		}
	}
	if len(names) == 0 {
		return ""
	}
	var sb strings.Builder
	for _, n := range names {
		sb.WriteString("\t_ = ")
		sb.WriteString(n)
		sb.WriteByte('\n')
	}
	return sb.String()
}

// docHarnessSetup writes a shared go.mod into root with replace directives
// pointing at the local repo's two Go modules. Returns the resolved
// fixture paths so wrapFence can substitute them per fence.
func docHarnessSetup(t *testing.T, root string) (yamlFix, excelFix string) {
	t.Helper()
	goDir := repoRootGoDir(t)
	yamlFix, _ = filepath.Abs("testdata/doc_examples/checks.yaml")
	if _, err := os.Stat(yamlFix); err != nil {
		t.Fatalf("missing yaml fixture: %v", err)
	}
	excelFix, _ = filepath.Abs(filepath.Join(goDir, "..", "examples", "demo", "demo_workbook.xlsx"))
	if _, err := os.Stat(excelFix); err != nil {
		t.Fatalf("missing excel fixture %s: %v", excelFix, err)
	}

	goMod := fmt.Sprintf(`module aletheia_doc_harness

go 1.24.0

toolchain go1.24.6

require (
	github.com/aletheia-automotive/aletheia-go v0.0.0
	github.com/aletheia-automotive/aletheia-go/excel v0.0.0
)

replace github.com/aletheia-automotive/aletheia-go => %s

replace github.com/aletheia-automotive/aletheia-go/excel => %s
`, goDir, filepath.Join(goDir, "excel"))
	if err := os.WriteFile(filepath.Join(root, "go.mod"), []byte(goMod), 0o644); err != nil {
		t.Fatalf("write go.mod: %v", err)
	}
	return yamlFix, excelFix
}

// TestDocExamples is the doc-fence executor. Each fence becomes a t.Run
// subtest reporting failure with file:line precision.
func TestDocExamples(t *testing.T) {
	lib := findFFILibForDocs()
	if lib == "" {
		t.Skip("libaletheia-ffi.so not found — run 'cabal run shake -- build' first")
	}

	root := t.TempDir()
	yamlFix, excelFix := docHarnessSetup(t, root)

	var fences []goFence
	for _, f := range docFiles {
		fences = append(fences, extractGoFences(t, f)...)
	}
	if len(fences) == 0 {
		t.Fatal("no ```go fences found across docFiles — likely a regression in extractGoFences or the file list")
	}

	// Materialize wrappers up-front so go.sum / module resolution happens once
	// (the first `go run` populates the per-module cache; subsequent fences
	// hit it). Each fence gets its own subdir / package main.
	type wrappedFence struct {
		fence   goFence
		dir     string
		pkgPath string
	}
	wrapped := make([]wrappedFence, 0, len(fences))
	for i, fence := range fences {
		body := substitutePaths(fence.content, lib, yamlFix, excelFix)
		src := wrapFence(body)
		dir := filepath.Join(root, "f"+strconv.Itoa(i))
		if err := os.MkdirAll(dir, 0o755); err != nil {
			t.Fatalf("mkdir %s: %v", dir, err)
		}
		if err := os.WriteFile(filepath.Join(dir, "main.go"), []byte(src), 0o644); err != nil {
			t.Fatalf("write main.go: %v", err)
		}
		wrapped = append(wrapped, wrappedFence{fence: fence, dir: dir, pkgPath: "./f" + strconv.Itoa(i)})
	}

	// Prime the module cache with one upfront `go build` so subsequent
	// per-fence runs share resolved deps and serialise the cgo lock once.
	// Without this, ~10 parallel `go run` calls hit the module cache lock
	// simultaneously and serialise anyway, plus the `go mod download`
	// pieces fight each other.
	primingCmd := exec.Command("go", "build", "-o", filepath.Join(root, "_prime"), wrapped[0].pkgPath)
	primingCmd.Dir = root
	primingCmd.Env = append(os.Environ(), "GOFLAGS=-mod=mod", "ALETHEIA_LIB="+lib)
	if out, err := primingCmd.CombinedOutput(); err != nil {
		t.Fatalf("priming build failed:\n%s\nerr: %v", out, err)
	}

	// concurrencyCap bounds parallel fence runs so RTS init races are bounded.
	// Empirically GHC RTS init can fail under heavy concurrent FFI loads;
	// runtime.NumCPU() is a generous ceiling that's still well below 11×.
	concurrencyCap := runtime.NumCPU()
	if concurrencyCap < 2 {
		concurrencyCap = 2
	}
	sem := make(chan struct{}, concurrencyCap)

	for _, w := range wrapped {
		w := w
		t.Run(w.fence.name(), func(t *testing.T) {
			t.Parallel()
			sem <- struct{}{}
			defer func() { <-sem }()

			cmd := exec.Command("go", "run", w.pkgPath)
			cmd.Dir = root
			cmd.Env = append(os.Environ(), "GOFLAGS=-mod=mod", "ALETHEIA_LIB="+lib)
			out, err := cmd.CombinedOutput()
			if err != nil {
				wrapper, _ := os.ReadFile(filepath.Join(w.dir, "main.go"))
				t.Fatalf("fence %s failed.\n----- WRAPPER (%s/main.go) -----\n%s\n----- COMBINED OUTPUT -----\n%s\n----- ERROR -----\n%v",
					w.fence.name(), w.dir, wrapper, out, err)
			}
		})
	}
}
