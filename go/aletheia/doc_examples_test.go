//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// The doc-example harness, the Go counterpart of the Python one under
// pytest --markdown-docs: every Go fence of the documents docFiles lists
// (doc_files_test.go, which holds that list to the tree) is extracted,
// wrapped as a program, compiled by one go build and run one at a time, in
// order; a fence that fails to build fails the test naming its file and
// line, and one that fails to run fails its subtest. Three literals are rewritten to fixtures first: the installed
// library path to the built library, checks.yaml to the test fixture, and
// checks.xlsx or tests.xlsx to the demo workbook. A fence is wrapped by its
// shape: one declaring package main runs verbatim; one opening with an
// import block gets package main and an empty main; a body fragment is
// placed inside a synthesised main with predeclared ctx, dbc, ts, canID, dlc,
// data, frames and libPath, and backend, client and parsed opened at its first
// use of one, so a fragment runs with the runtime down until then, as a
// reader's program does until it starts the runtime; every name it declares
// with := is used once so an unused variable cannot fail it. The gates in
// doc_files_test.go hold the list to the tree and refuse a Go fence hidden
// behind a suffixed info word; a fence that cannot run opens with tildes,
// which the extractor does not read.
package aletheia_test

import (
	"bufio"
	"cmp"
	"encoding/json"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"os/exec"
	"path/filepath"
	"reflect"
	"regexp"
	"slices"
	"strconv"
	"strings"
	"testing"

	"github.com/Jaetan/aletheia/go/v5/aletheia"
)

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
// package and an empty main, anything else is a body fragment. Each shape
// has its discarded errors checked (rewriteDiscards) and carries the
// function that checks them.
func wrapFence(body, doc string, opening int, funcs map[string]bool) string {
	if packageName(body) != "" {
		return rewriteDiscards(body, "", "", doc, opening, funcs) + discardedErrors
	}
	if hasImportBlock(body) {
		const head = "package main\n\n"
		return head + rewriteDiscards(body, head, "", doc, opening, funcs) + "\nfunc main() {}\n" + discardedErrors
	}
	return wrapBodyFragment(rewriteDiscards(body, fragmentHead, fragmentTail, doc, opening, funcs), doc, opening)
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
// predeclared names are the Python harness's globals, the backend and the
// client among them opened at the fragment's first evaluation of one
// (withHarnessClient),
// and hands every name the fragment declares with := and never reads to
// docExampleDiscarded, so an unused variable cannot fail it and an unread
// error ends the run.
func wrapBodyFragment(body, doc string, opening int) string {
	suppressors := unusedSuppressors(body, doc, opening)
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

%s
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
	dbcDef := buildDocDBC()

	var ts aletheia.Timestamp
	canID, _ := aletheia.NewStandardID(0x100)
	dlc, _ := aletheia.NewDLC(8)
	data := aletheia.FramePayload(make([]byte, 8))
	frames := []aletheia.Frame{}
	dbc := dbcDef
	_, _, _, _, _, _ = ts, canID, dlc, data, frames, dbc

	// The harness's backend, a client over it that parsed the DBC above, and
	// what the parse returned, opened at the fence's first evaluation of one,
	// which withHarnessClient rewrites to these calls.
	var docHarness struct {
		backend *aletheia.FFIBackend
		client  *aletheia.Client
		parsed  *aletheia.ParsedDBC
	}
	defer func() {
		if docHarness.client != nil {
			_ = docHarness.client.Close()
		}
	}()
	docHarnessOpen := func() {
		if docHarness.client != nil {
			return
		}
		var err error
		if docHarness.backend, err = aletheia.NewFFIBackend(libPath, aletheia.WithFFILogger(slog.Default())); err != nil {
			panic(err)
		}
		if docHarness.client, err = aletheia.NewClient(docHarness.backend, aletheia.WithLogger(slog.Default())); err != nil {
			panic(err)
		}
		if docHarness.parsed, err = docHarness.client.ParseDBC(ctx, dbcDef); err != nil {
			panic(err)
		}
	}
	docHarnessBackend := func() *aletheia.FFIBackend { docHarnessOpen(); return docHarness.backend }
	docHarnessClient := func() *aletheia.Client { docHarnessOpen(); return docHarness.client }
	docHarnessParsed := func() *aletheia.ParsedDBC { docHarnessOpen(); return docHarness.parsed }
	_, _, _ = docHarnessBackend, docHarnessClient, docHarnessParsed

	// a nested block, so a fence that redeclares a predeclared name with
	// := shadows it instead of failing
	{
		// ====== FENCE BODY START ======
%s
		// ====== FENCE BODY END ======
%s
	}
	_, _ = ctx, libPath
}
`
	return fmt.Sprintf(tmpl, discardedErrors, body, suppressors)
}

// harnessOpeners are the predeclared names the harness's backend, client and
// parsed DBC stand behind, each with the main's function that opens the three
// at its first call.
var harnessOpeners = map[string]string{
	"backend": "docHarnessBackend",
	"client":  "docHarnessClient",
	"parsed":  "docHarnessParsed",
}

// namedHarness matches a fragment spelling one of harnessOpeners: only such
// a fragment needs the compiler's report of its undeclared uses before it runs.
var namedHarness = regexp.MustCompile(`\b(?:backend|client|parsed)\b`)

// harnessUse is a use of one of harnessOpeners the compiler found no
// declaration of: the line and the column, a byte's, it reports.
type harnessUse struct {
	line, column int
	name         string
}

// reportedHarness matches the compiler's `<dir>/main.go:<line>:<column>:
// undefined: client`, the declarations a fragment writes itself, in any form,
// being the compiler's to tell apart.
var reportedHarness = regexp.MustCompile(`(?m)^(?:\./)?(f\d+)/main\.go:(\d+):(\d+): undefined: (backend|client|parsed)$`)

// reportedHarnessUses is the uses a build's output reports undeclared, by the
// directory of the program holding them.
func reportedHarnessUses(output string) map[string][]harnessUse {
	uses := map[string][]harnessUse{}
	for _, m := range reportedHarness.FindAllStringSubmatch(output, -1) {
		line, _ := strconv.Atoi(m[2])
		column, _ := strconv.Atoi(m[3])
		uses[m[1]] = append(uses[m[1]], harnessUse{line: line, column: column, name: m[4]})
	}
	return uses
}

// withHarnessClient is src with each of uses calling the harness's opener of
// its name, so the harness's backend and client, and the runtime with them,
// open at the fragment's first evaluation of one: until then the runtime is
// down, as a reader's program finds it until it starts the runtime or opens a
// client, so a fragment reading a number first fails here as it would there.
func withHarnessClient(src string, uses []harnessUse) string {
	starts := []int{0}
	for i, c := range src {
		if c == '\n' {
			starts = append(starts, i+1)
		}
	}
	uses = slices.Clone(uses)
	slices.SortFunc(uses, func(a, b harnessUse) int {
		return cmp.Or(cmp.Compare(b.line, a.line), cmp.Compare(b.column, a.column))
	})
	uses = slices.Compact(uses)
	for _, use := range uses {
		at := starts[use.line-1] + use.column - 1
		src = src[:at] + harnessOpeners[use.name] + "()" + src[at+len(use.name):]
	}
	return src
}

// harnessUsesOf builds the programs in dirs (directories of root, the module
// docHarnessSetup writes) once with every compile error reported, and returns
// the uses of harnessOpeners each leaves undeclared.
func harnessUsesOf(t *testing.T, root string, env, dirs []string) map[string][]harnessUse {
	t.Helper()
	if len(dirs) == 0 {
		return nil
	}
	args := []string{"build", "-gcflags=-e", "-o", t.TempDir() + string(filepath.Separator)}
	for _, dir := range dirs {
		args = append(args, "./"+dir)
	}
	build := exec.Command("go", args...)
	build.Dir = root
	build.Env = env
	out, _ := build.CombinedOutput()
	return reportedHarnessUses(string(out))
}

// unusedSuppressors is one docExampleDiscarded call per name the fragment
// declares with := at its top level and never reads (a name declared inside
// a block is scoped there and needs none). A fragment that does not parse
// gets none; the build then reports the real error with its position.
func unusedSuppressors(body, doc string, opening int) string {
	src := fragmentHead + body + fragmentTail
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
	// A name is read when it appears anywhere but where it is declared.
	appearances := map[string]int{}
	ast.Inspect(fn.Body, func(node ast.Node) bool {
		if id, ok := node.(*ast.Ident); ok {
			appearances[id.Name]++
		}
		return true
	})
	var sb strings.Builder
	seen := map[string]bool{}
	for _, stmt := range fn.Body.List {
		as, ok := stmt.(*ast.AssignStmt)
		if !ok || as.Tok != token.DEFINE {
			continue
		}
		for _, lhs := range as.Lhs {
			id, ok := lhs.(*ast.Ident)
			if !ok || id.Name == "_" || seen[id.Name] || appearances[id.Name] > 1 {
				continue
			}
			seen[id.Name] = true
			fmt.Fprintf(&sb, "\tdocExampleDiscarded(%q, %s)\n", discardSite(doc, opening, fset.Position(id.Pos()).Line, fragmentHead), id.Name)
		}
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
	excelFix, _ = filepath.Abs(filepath.Join(aletheia.RepoRoot(t), "examples", "demo", "demo_workbook.xlsx"))
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

// refusalCodes is the code of each refusal the forwarding stand-in logged
// to path, in order: a line is the entry, a tab and the kernel's envelope.
// No file is no refusal.
func refusalCodes(t *testing.T, path string) []string {
	t.Helper()
	data, err := os.ReadFile(path)
	if os.IsNotExist(err) {
		return nil
	}
	if err != nil {
		t.Fatalf("read the refusal log: %v", err)
	}
	var codes []string
	scanner := bufio.NewScanner(strings.NewReader(string(data)))
	scanner.Buffer(make([]byte, 1024*1024), 1024*1024)
	for scanner.Scan() {
		_, envelope, ok := strings.Cut(scanner.Text(), "\t")
		var refusal struct {
			Code string `json:"code"`
		}
		if !ok || json.Unmarshal([]byte(envelope), &refusal) != nil || refusal.Code == "" {
			t.Fatalf("an unreadable refusal log line: %q", scanner.Text())
		}
		codes = append(codes, refusal.Code)
	}
	return codes
}

// Every Go fence of every listed file builds and runs, each as its own
// subtest named by file and line, against the forwarding stand-in kernel:
// a fence fails unless the kernel refused exactly the codes the line
// directly above it names, so one that discards a refused call fails too.
func TestDocExamples(t *testing.T) {
	lib := findFFILibForDocs()
	if lib == "" {
		t.Skip("libaletheia-ffi.so not found; run 'cabal run shake -- build' first")
	}
	forwarder := aletheia.StandIn(t, lib, "forwarding_kernel")
	funcs, err := errorReturning()
	if err != nil {
		t.Fatalf("read the bindings' sources: %v", err)
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
		body := substitutePaths(fence.content, forwarder, yamlFix, excelFix)
		src := wrapFence(body, fence.file, fence.line, funcs)
		dir := filepath.Join(root, "f"+strconv.Itoa(i))
		if err := os.MkdirAll(dir, 0o755); err != nil {
			t.Fatalf("mkdir %s: %v", dir, err)
		}
		if err := os.WriteFile(filepath.Join(dir, "main.go"), []byte(src), 0o644); err != nil {
			t.Fatalf("write main.go: %v", err)
		}
		wrapped = append(wrapped, wrappedFence{fence: fence, dir: dir, pkgPath: "./f" + strconv.Itoa(i)})
	}

	env := append(os.Environ(), "GOFLAGS=-mod=mod", "ALETHEIA_LIB="+forwarder, "ALETHEIA_FORWARD_TO="+lib)
	// a fence naming the harness's backend, client or parsed DBC is built
	// once first, its undeclared uses taken from the compiler's report
	var naming []string
	for _, w := range wrapped {
		if namedHarness.MatchString(w.fence.content) {
			naming = append(naming, filepath.Base(w.dir))
		}
	}
	for dir, uses := range harnessUsesOf(t, root, env, naming) {
		path := filepath.Join(root, dir, "main.go")
		src, err := os.ReadFile(path)
		if err != nil {
			t.Fatalf("read %s: %v", path, err)
		}
		if err := os.WriteFile(path, []byte(withHarnessClient(string(src), uses)), 0o644); err != nil {
			t.Fatalf("write %s: %v", path, err)
		}
	}

	// one build compiles every fence into bin/, a program per fence named
	// as its directory; a fence that does not compile is named by the
	// build's own "# aletheia_doc_harness/fN" header, mapped back below
	bin := filepath.Join(root, "bin") + string(filepath.Separator)
	args := []string{"build", "-o", bin}
	for _, w := range wrapped {
		args = append(args, w.pkgPath)
	}
	build := exec.Command("go", args...)
	build.Dir = root
	build.Env = env
	if out, err := build.CombinedOutput(); err != nil {
		var names strings.Builder
		for _, w := range wrapped {
			fmt.Fprintf(&names, "  aletheia_doc_harness/%s is %s\n", filepath.Base(w.dir), w.fence.name())
		}
		t.Fatalf("the fences do not build:\n%s\nerr: %v\n----- FENCES -----\n%s", out, err, names.String())
	}

	// each fence then runs alone, in document order
	for _, w := range wrapped {
		t.Run(w.fence.name(), func(t *testing.T) {
			refusals := filepath.Join(w.dir, "refusals.log")
			cmd := exec.Command(filepath.Join(bin, filepath.Base(w.dir)))
			cmd.Dir = root
			cmd.Env = append(slices.Clip(env), "ALETHEIA_REFUSAL_LOG="+refusals)
			out, err := cmd.CombinedOutput()
			if err != nil {
				wrapper, _ := os.ReadFile(filepath.Join(w.dir, "main.go"))
				t.Fatalf("fence %s failed.\n----- WRAPPER (%s/main.go) -----\n%s\n----- COMBINED OUTPUT -----\n%s\n----- ERROR -----\n%v",
					w.fence.name(), w.dir, wrapper, out, err)
			}
			if refused := refusalCodes(t, refusals); !slices.Equal(refused, w.fence.refuses) {
				log, _ := os.ReadFile(refusals)
				t.Fatalf("fence %s: the kernel refused %v, the fence states %v: an example that shows a refusal names its codes on a `<!-- refuses: <code> ... -->` line directly above its fence\n%s",
					w.fence.name(), refused, w.fence.refuses, log)
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

// TestWithHarnessClient holds the report's reading and the rewrite: each
// reported use calls the opener of its name, a repeated report once.
func TestWithHarnessClient(t *testing.T) {
	out := "# aletheia_doc_harness/f3\nf3/main.go:3:5: undefined: client\n./f3/main.go:4:9: undefined: backend\n" +
		"f4/main.go:1:1: undefined: load\nf5/main.go:2:2: undefined: parsed\n"
	want := map[string][]harnessUse{
		"f3": {{line: 3, column: 5, name: "client"}, {line: 4, column: 9, name: "backend"}},
		"f5": {{line: 2, column: 2, name: "parsed"}},
	}
	if got := reportedHarnessUses(out); !reflect.DeepEqual(got, want) {
		t.Errorf("reportedHarnessUses\n got %v\nwant %v", got, want)
	}
	uses := []harnessUse{{line: 2, column: 2, name: "client"}, {line: 2, column: 11, name: "backend"}, {line: 2, column: 2, name: "client"}}
	if got, want := withHarnessClient("a\n\tclient.X(backend)\n", uses), "a\n\tdocHarnessClient().X(docHarnessBackend())\n"; got != want {
		t.Errorf("withHarnessClient\n got %q\nwant %q", got, want)
	}
}

// TestTheCompilerNamesTheHarnessUses builds a fragment in the forms a fence
// declares the harness's names in itself (its own client over the harness's
// backend, a block's own, a parameter, a struct field and a literal's key, a
// string and a comment) and holds the rewrite to the uses it leaves
// undeclared: one in a loop after a read, the backend, the parsed DBC.
func TestTheCompilerNamesTheHarnessUses(t *testing.T) {
	root := t.TempDir()
	docHarnessSetup(t, root)
	written := "limit := 1\nfor range limit {\n\t_ = client\n}\n{\n\tclient, err := aletheia.NewClient(backend)\n" +
		"\t_, _ = client, err\n}\n{\n\tclient := 1\n\t_ = client\n}\nf := func(backend int) int { return backend + 1 }\n" +
		"type holder struct{ client int }\nh := holder{client: f(1)}\n_ = h.client\n_ = \"client\" // client\n_ = parsed\n"
	expected := strings.NewReplacer(
		"\t_ = client\n}\n{\n\tclient, err", "\t_ = docHarnessClient()\n}\n{\n\tclient, err",
		"NewClient(backend)", "NewClient(docHarnessBackend())",
		"_ = parsed\n", "_ = docHarnessParsed()\n",
	).Replace(written)
	program := wrapBodyFragment(written, "sample.md", 1)
	dir := filepath.Join(root, "f0")
	if err := os.MkdirAll(dir, 0o755); err != nil {
		t.Fatalf("mkdir %s: %v", dir, err)
	}
	if err := os.WriteFile(filepath.Join(dir, "main.go"), []byte(program), 0o644); err != nil {
		t.Fatalf("write main.go: %v", err)
	}
	uses := harnessUsesOf(t, root, append(os.Environ(), "GOFLAGS=-mod=mod"), []string{"f0"})
	if got, want := withHarnessClient(program, uses["f0"]), wrapBodyFragment(expected, "sample.md", 1); got != want {
		t.Errorf("the rewrite of the compiler's report\n got %s\nwant %s", got, want)
	}
}
