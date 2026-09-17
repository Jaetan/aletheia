//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// The doc-example harness, the Go counterpart of the Python one under
// pytest --markdown-docs: every Go fence in the listed Markdown files is
// extracted, wrapped as a program, compiled and run through go run, and a
// fence that fails to build or to run fails the test under its file and
// line. Three literals are rewritten to fixtures first: the installed
// library path to the built library, checks.yaml to the test fixture, and
// checks.xlsx or tests.xlsx to the demo workbook. A fence is wrapped by its
// shape: one declaring package main runs verbatim; one opening with an
// import block gets package main and an empty main; a body fragment is
// placed inside a synthesised main with predeclared ctx, client, dbc, ts,
// canID, dlc, data, frames and libPath, and every name it declares with :=
// is used once so an unused variable cannot fail it. The companion gate in
// doc_no_notest_test.go refuses the notest annotation; a fence that cannot
// run takes the text info string.
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

	"github.com/Jaetan/aletheia/go/v5/aletheia"
)

// docFiles is every user-facing Markdown file with Go fences, relative to
// this directory; a tracked file with a Go fence that is not listed is what
// the probe over this file catches. CHANGELOG.md stays out on purpose.
var docFiles = []string{
	"../README.md",
	"../../README.md",
	"../../docs/PITCH.md",
	"../../docs/architecture/CANCELLATION.md",
	"../../docs/reference/INTERFACES.md",
	"../../docs/reference/GO_API.md",
	"../../docs/development/DISTRIBUTION.md",
	"../../docs/guides/TUTORIAL.md",
}

// goFence is one Go fence of a listed file.
type goFence struct {
	file    string // repo-relative path
	line    int    // 1-based line number of the opening ```go
	content string // body between fences (no surrounding ``` lines)
}

func (f goFence) name() string {
	// subtest names are repository-relative
	name := strings.TrimPrefix(f.file, "../../")
	if strings.HasPrefix(name, "../") {
		name = "go/" + strings.TrimPrefix(name, "../")
	}
	return fmt.Sprintf("%s:L%d", name, f.line)
}

// extractGoFences returns every Go fence of one file: an opening line whose
// info string is exactly go, closed by a line that is exactly the fence.
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

// findFFILibForDocs is the binding's library search (ALETHEIA_LIB, then
// the build tree relative to the package), repeated here because the
// package's own search is unexported to this test package.
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

// repoRootGoDir is the absolute path of the go module directory, the
// target of the synthesised go.mod's replace directive.
func repoRootGoDir(t *testing.T) string {
	t.Helper()
	abs, err := filepath.Abs("..")
	if err != nil {
		t.Fatalf("abs ..: %v", err)
	}
	return abs
}

// substitutePaths rewrites the three fixture literals a fence may quote to
// the paths present at test time, at the source level, since Go cannot
// swap functions at run time the way the Python conftest does.
func substitutePaths(body, libPath, yamlFix, excelFix string) string {
	body = strings.ReplaceAll(body, `"/opt/aletheia/lib/libaletheia-ffi.so"`, strconv.Quote(libPath))
	body = strings.ReplaceAll(body, `"checks.yaml"`, strconv.Quote(yamlFix))
	body = strings.ReplaceAll(body, `"checks.xlsx"`, strconv.Quote(excelFix))
	body = strings.ReplaceAll(body, `"tests.xlsx"`, strconv.Quote(excelFix))
	return body
}

// wrapFence returns the fence as a main.go, by its shape: a package clause
// (which comments may precede) runs verbatim, an import block gets a
// package and an empty main, anything else is a body fragment.
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
		return false
	}
	return false
}

// wrapBodyFragment places a fragment inside a synthesised main whose
// predeclared names are the Python harness's globals, and uses every name
// the fragment declares with := so an unused variable cannot fail it.
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

	"github.com/Jaetan/aletheia/go/v5/aletheia"
	"github.com/Jaetan/aletheia/go/excel"
)

// the fence may leave any of these imports unused
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

func buildDocDBC() aletheia.DBCDefinition {
	rat := func(n, d int64) aletheia.Rational { return aletheia.Rational{Numerator: n, Denominator: d} }
	signal := func(name aletheia.SignalName, start aletheia.BitPosition, length aletheia.BitLength, maxVal int64) aletheia.DBCSignal {
		return aletheia.DBCSignal{
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
	// 0x100 carries the streaming fences' signals, 0x110 the ones the YAML
	// check fences name
	sid2, _ := aletheia.NewStandardID(0x110)
	return aletheia.DBCDefinition{
		Version: "1.0",
		Messages: []aletheia.DBCMessage{
			{
				ID:     sid,
				Name:   "VehicleState",
				DLC:    dlc,
				Sender: "ECU",
				Signals: []aletheia.DBCSignal{
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
				Signals: []aletheia.DBCSignal{
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

	// a nested block, so a fence that redeclares a predeclared name with
	// := shadows it instead of failing
	{
		// ====== FENCE BODY START ======
%s
		// ====== FENCE BODY END ======
%s
	}
	_ = ctx
	_ = backend
	_ = client
}
`
	return fmt.Sprintf(tmpl, body, suppressors)
}

// unusedSuppressors is one blank assignment per name the fragment declares
// with := at its top level (a name declared inside a block is scoped there
// and needs none). A fragment that does not parse gets none; go run then
// reports the real error with its position.
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

// docHarnessSetup writes the shared go.mod, whose replace directives point
// at the repository's two Go modules, and returns the fixture paths.
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
	github.com/Jaetan/aletheia/go/v5 v5.0.0
	github.com/Jaetan/aletheia/go/excel v0.0.0
)

replace github.com/Jaetan/aletheia/go/v5 => %s

replace github.com/Jaetan/aletheia/go/excel => %s
`, goDir, filepath.Join(goDir, "excel"))
	if err := os.WriteFile(filepath.Join(root, "go.mod"), []byte(goMod), 0o644); err != nil {
		t.Fatalf("write go.mod: %v", err)
	}
	return yamlFix, excelFix
}

// Every Go fence of every listed file builds and runs, each as its own
// subtest named by file and line.
func TestDocExamples(t *testing.T) {
	lib := findFFILibForDocs()
	if lib == "" {
		t.Skip("libaletheia-ffi.so not found; run 'cabal run shake -- build' first")
	}

	root := t.TempDir()
	yamlFix, excelFix := docHarnessSetup(t, root)

	var fences []goFence
	for _, f := range docFiles {
		fences = append(fences, extractGoFences(t, f)...)
	}
	if len(fences) == 0 {
		t.Fatal("no Go fence found across docFiles: the extractor or the list has regressed")
	}

	// every fence is written first, each in its own directory
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

	// one build first resolves the modules and warms the cache, so the
	// parallel runs below do not race for the module lock
	primingCmd := exec.Command("go", "build", "-o", filepath.Join(root, "_prime"), wrapped[0].pkgPath)
	primingCmd.Dir = root
	primingCmd.Env = append(os.Environ(), "GOFLAGS=-mod=mod", "ALETHEIA_LIB="+lib)
	if out, err := primingCmd.CombinedOutput(); err != nil {
		t.Fatalf("priming build failed:\n%s\nerr: %v", out, err)
	}

	// parallel runs are capped at the CPU count, since the GHC runtime's
	// initialisation has failed under heavier concurrent loads
	sem := make(chan struct{}, max(runtime.NumCPU(), 2))

	for _, w := range wrapped {
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

// The checks fixture the fences load is loaded here too, and read. Those
// fences discard what they loaded, as a caller's first line would, so without
// this nothing would notice a fixture that stopped parsing or that named a
// condition the loader does not know.
func TestDocExamplesFixture_ChecksYAMLLoads(t *testing.T) {
	path, err := filepath.Abs("testdata/doc_examples/checks.yaml")
	if err != nil {
		t.Fatalf("abs: %v", err)
	}
	checks, err := aletheia.LoadChecksFromYAMLFile(path)
	if err != nil {
		t.Fatalf("the fixture the documentation loads does not load: %v", err)
	}
	if len(checks) != 2 {
		t.Fatalf("the fixture carries %d checks, want the two the documentation describes", len(checks))
	}
	for _, c := range checks {
		if c.Formula() == nil {
			t.Errorf("a check of the fixture carries no formula: %+v", c)
		}
	}
}
