// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Command aletheia is the Go host CLI for the Aletheia CAN signal
// verification core. It mirrors the Python `python -m aletheia` subcommand
// surface — validate, extract, signals, format-dbc, mux-query — by
// dispatching to the real verified Agda core through the cgo/dlopen client
// (no analysis logic is reimplemented here; the CLI is plumbing only).
//
// The `check` subcommand (LTL evaluation over a CAN log file) is
// intentionally absent: it requires a verified CAN-log reader the Go
// binding does not yet provide, tracked as a Phase 6 item (the python-can
// replacement). DBC sources are `.dbc` text files parsed by the verified
// text parser; canonical-JSON and `.xlsx` inputs are not yet wired.
//
// Flags may appear before or after positionals (reorderArgs normalizes the
// order before stdlib flag parsing, matching the Python argparse UX), e.g.:
//
//	aletheia extract --dbc vehicle.dbc 0x100 401F7D0000000000
//	aletheia mux-query --dbc vehicle.dbc 0x100 --mux Mode --value 5
//
// The library path is resolved from $ALETHEIA_LIB, else common build/install
// locations. Exit codes: 0 ok, 1 violations / validation failed, 2 error.
package main

import (
	"context"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"os"
	"strconv"
	"strings"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

const (
	exitOK         = 0
	exitViolations = 1
	exitError      = 2
)

func main() {
	os.Exit(run(os.Args[1:]))
}

func run(argv []string) int {
	if len(argv) == 0 {
		fmt.Fprintln(os.Stderr, usage)
		return exitError
	}
	cmd, rest := argv[0], argv[1:]
	switch cmd {
	case "validate":
		return cmdValidate(rest)
	case "extract":
		return cmdExtract(rest)
	case "signals":
		return cmdSignals(rest)
	case "format-dbc":
		return cmdFormatDBC(rest)
	case "mux-query":
		return cmdMuxQuery(rest)
	case "check":
		fmt.Fprintln(os.Stderr, "Error: 'check' is not available in the Go CLI yet — "+
			"it needs a verified CAN-log reader (Phase 6: python-can replacement). "+
			"Use the Python CLI for log-file checking.")
		return exitError
	case "-h", "--help", "help":
		fmt.Println(usage)
		return exitOK
	default:
		fmt.Fprintf(os.Stderr, "Error: unknown command %q\n\n%s\n", cmd, usage)
		return exitError
	}
}

const usage = `aletheia — formally verified CAN signal analysis (Go CLI)

Usage: aletheia <command> [flags] [args]

Commands:
  validate    validate a DBC definition for structural issues
  extract     decode signals from a single CAN frame
  signals     list signals defined in a DBC file
  format-dbc  re-export a DBC as canonical JSON via the Agda core
  mux-query   inspect multiplexor structure of a DBC message

DBC source: --dbc <file>.dbc (verified text parser). Flags may go before or after positionals.
Library path: $ALETHEIA_LIB or a build/install default.`

// --- shared helpers -------------------------------------------------------

func die(msg string) int {
	fmt.Fprintf(os.Stderr, "Error: %s\n", msg)
	return exitError
}

// newFlagSet builds a per-subcommand flag set that reports parse errors to
// the caller (ContinueOnError) instead of calling os.Exit, so run() owns
// the process exit code.
func newFlagSet(name string) *flag.FlagSet {
	return flag.NewFlagSet(name, flag.ContinueOnError)
}

// reorderArgs moves flag tokens (and their values) ahead of positional
// arguments so flags may appear after positionals — matching the Python
// CLI's argparse behavior. Go's flag package otherwise stops at the first
// non-flag token. boolFlags names the flags that take no value.
func reorderArgs(argv []string, boolFlags map[string]bool) []string {
	flags := make([]string, 0, len(argv))
	pos := make([]string, 0, len(argv))
	for i := 0; i < len(argv); i++ {
		a := argv[i]
		if a == "--" {
			pos = append(pos, argv[i+1:]...)
			break
		}
		if !strings.HasPrefix(a, "-") || a == "-" {
			pos = append(pos, a)
			continue
		}
		flags = append(flags, a)
		name := strings.TrimLeft(a, "-")
		// "--flag value" form: pull the value too, unless it's a bool flag
		// or already "--flag=value".
		if !strings.ContainsRune(name, '=') && !boolFlags[name] && i+1 < len(argv) {
			flags = append(flags, argv[i+1])
			i++
		}
	}
	return append(flags, pos...)
}

// resolveLib finds libaletheia-ffi.so: $ALETHEIA_LIB, then common
// build/install locations. Returns "" if none exist.
func resolveLib() string {
	if env := os.Getenv("ALETHEIA_LIB"); env != "" {
		return env
	}
	for _, p := range []string{
		"build/libaletheia-ffi.so",
		"../build/libaletheia-ffi.so",
		"../../build/libaletheia-ffi.so",
		"/usr/local/lib/libaletheia-ffi.so",
	} {
		if _, err := os.Stat(p); err == nil {
			return p
		}
	}
	return ""
}

// newClient builds a client over the real FFI backend.
func newClient() (*aletheia.Client, error) {
	lib := resolveLib()
	if lib == "" {
		return nil, fmt.Errorf("libaletheia-ffi.so not found; set $ALETHEIA_LIB or run 'cabal run shake -- build'")
	}
	backend, err := aletheia.NewFFIBackend(lib)
	if err != nil {
		return nil, fmt.Errorf("loading %s: %w", lib, err)
	}
	return aletheia.NewClient(backend)
}

// loadDBCText reads a .dbc text file and parses it through the verified
// Agda text parser. Canonical-JSON and .xlsx inputs are not yet wired.
func loadDBCText(client *aletheia.Client, path string) (aletheia.DBCDefinition, error) {
	if path == "" {
		return aletheia.DBCDefinition{}, fmt.Errorf("no DBC source (use --dbc <file>.dbc)")
	}
	if strings.HasSuffix(path, ".json") || strings.HasSuffix(path, ".xlsx") {
		return aletheia.DBCDefinition{}, fmt.Errorf("%s: only .dbc text input is supported by the Go CLI yet "+
			"(JSON / .xlsx input not wired)", path)
	}
	raw, err := os.ReadFile(path)
	if err != nil {
		return aletheia.DBCDefinition{}, fmt.Errorf("reading %s: %w", path, err)
	}
	parsed, err := client.ParseDBCText(context.Background(), string(raw))
	if err != nil {
		return aletheia.DBCDefinition{}, fmt.Errorf("parsing %s: %w", path, err)
	}
	return parsed.DBC, nil
}

func parseCANID(s string) (uint32, error) {
	s = strings.TrimSpace(s)
	if strings.HasPrefix(strings.ToLower(s), "0x") {
		v, err := strconv.ParseUint(s[2:], 16, 32)
		return uint32(v), err
	}
	v, err := strconv.ParseUint(s, 10, 32)
	return uint32(v), err
}

func makeCANID(n uint32, extended bool) (aletheia.CANID, error) {
	if extended {
		id, err := aletheia.NewExtendedID(n)
		return id, err
	}
	if n > 0x7FF {
		return nil, fmt.Errorf("standard CAN ID 0x%X exceeds 11 bits (use --extended)", n)
	}
	id, err := aletheia.NewStandardID(uint16(n))
	return id, err
}

func parseHexData(s string) ([]byte, error) {
	cleaned := strings.NewReplacer(" ", "", ":", "").Replace(s)
	cleaned = strings.TrimPrefix(strings.ToLower(cleaned), "0x")
	if len(cleaned)%2 != 0 {
		return nil, fmt.Errorf("hex data has odd number of characters: %q", s)
	}
	out := make([]byte, len(cleaned)/2)
	for i := 0; i < len(out); i++ {
		b, err := strconv.ParseUint(cleaned[2*i:2*i+2], 16, 8)
		if err != nil {
			return nil, fmt.Errorf("invalid hex data: %q", s)
		}
		out[i] = byte(b)
	}
	return out, nil
}

func emitJSON(v any) int {
	b, err := json.MarshalIndent(v, "", "  ")
	if err != nil {
		return die(fmt.Sprintf("encoding JSON: %v", err))
	}
	fmt.Println(string(b))
	return exitOK
}

// --- validate -------------------------------------------------------------

func cmdValidate(argv []string) int {
	fs := newFlagSet("validate")
	dbc := fs.String("dbc", "", ".dbc file for signal definitions")
	asJSON := fs.Bool("json", false, "output as JSON")
	if err := fs.Parse(argv); err != nil {
		return exitError
	}
	client, err := newClient()
	if err != nil {
		return die(err.Error())
	}
	def, err := loadDBCText(client, *dbc)
	if err != nil {
		// A DBC that parses syntactically but fails structural validation
		// carries the same has_errors/issues payload as a ValidateDBC
		// result — render it identically (issue list, exit 1) instead of
		// dying with the bare message. A syntactically-unparseable DBC has
		// no issues payload and still dies below.
		var vfe *aletheia.ValidationFailedError
		if errors.As(err, &vfe) {
			return renderValidation(vfe.HasErrors, vfe.Issues, *asJSON)
		}
		return die(err.Error())
	}
	res, err := client.ValidateDBC(context.Background(), def)
	if err != nil {
		return die(err.Error())
	}
	return renderValidation(res.HasErrors, res.Issues, *asJSON)
}

// renderValidation emits the validate subcommand's result — JSON or text —
// from the has_errors/issues pair shared by a ValidateDBC result and a
// parse-time ValidationFailedError.
func renderValidation(hasErrors bool, resIssues []aletheia.ValidationIssue, asJSON bool) int {
	if asJSON {
		issues := make([]map[string]any, 0, len(resIssues))
		for _, i := range resIssues {
			issues = append(issues, map[string]any{
				"severity": i.Severity.String(),
				"code":     string(i.Code),
				"detail":   i.Detail,
			})
		}
		status := "pass"
		if hasErrors {
			status = "fail"
		}
		code := emitJSON(map[string]any{
			"status":       status,
			"has_errors":   hasErrors,
			"total_issues": len(resIssues),
			"issues":       issues,
		})
		// The exit code reflects the validation outcome in both output
		// modes — a pipeline running --json still needs exit 1 on failure.
		if hasErrors {
			return exitViolations
		}
		return code
	}
	if len(resIssues) == 0 {
		fmt.Println("Validation passed: no issues found")
		return exitOK
	}
	if hasErrors {
		fmt.Printf("Validation FAILED (%d issues)\n\n", len(resIssues))
	} else {
		fmt.Printf("Validation passed with %d warnings\n\n", len(resIssues))
	}
	for n, i := range resIssues {
		fmt.Printf("  %d. [%s] %s: %s\n", n+1, strings.ToUpper(i.Severity.String()), string(i.Code), i.Detail)
	}
	if hasErrors {
		return exitViolations
	}
	return exitOK
}

// --- extract --------------------------------------------------------------

func cmdExtract(argv []string) int {
	fs := newFlagSet("extract")
	dbc := fs.String("dbc", "", ".dbc file (required)")
	extended := fs.Bool("extended", false, "treat CAN ID as 29-bit extended")
	asJSON := fs.Bool("json", false, "output as JSON")
	if err := fs.Parse(reorderArgs(argv, map[string]bool{"extended": true, "json": true})); err != nil {
		return exitError
	}
	if fs.NArg() != 2 {
		return die("extract requires <can_id> <data> positional arguments")
	}
	canID, err := parseCANID(fs.Arg(0))
	if err != nil {
		return die(fmt.Sprintf("invalid CAN ID %q", fs.Arg(0)))
	}
	data, err := parseHexData(fs.Arg(1))
	if err != nil {
		return die(err.Error())
	}
	client, err := newClient()
	if err != nil {
		return die(err.Error())
	}
	def, err := loadDBCText(client, *dbc)
	if err != nil {
		return die(err.Error())
	}
	id, err := makeCANID(canID, *extended)
	if err != nil {
		return die(err.Error())
	}
	msg := def.MessageByID(id)
	if msg == nil {
		kind := "standard"
		if *extended {
			kind = "extended"
		}
		return die(fmt.Sprintf("CAN ID 0x%X (%s) not found in DBC", canID, kind))
	}
	if len(data) != msg.DLC.ToBytes() {
		return die(fmt.Sprintf("data length (%d bytes) does not match DBC message DLC (%d bytes)", len(data), msg.DLC.ToBytes()))
	}
	if _, err := client.ParseDBC(context.Background(), def); err != nil {
		return die(err.Error())
	}
	res, err := client.ExtractSignals(context.Background(), id, msg.DLC, aletheia.FramePayload(data))
	if err != nil {
		return die(err.Error())
	}
	if *asJSON {
		values := make(map[string]any, len(res.Values))
		for _, v := range res.Values {
			values[string(v.Name)] = rationalJSON(v.Value)
		}
		errs := make(map[string]string, len(res.Errors))
		for _, e := range res.Errors {
			errs[string(e.Name)] = e.Error
		}
		absent := make([]string, 0, len(res.Absent))
		for _, a := range res.Absent {
			absent = append(absent, string(a))
		}
		return emitJSON(map[string]any{
			"can_id":   canID,
			"extended": *extended,
			"values":   values,
			"errors":   errs,
			"absent":   absent,
		})
	}
	units := map[string]string{}
	for _, sig := range msg.Signals {
		units[string(sig.Name)] = string(sig.Unit)
	}
	fmt.Printf("CAN ID 0x%X (%s):\n\n", canID, msg.Name)
	if len(res.Values) == 0 {
		fmt.Println("  (no signals)")
	}
	for _, v := range res.Values {
		unit := units[string(v.Name)]
		if unit != "" {
			unit = " " + unit
		}
		// Exact rational render (kernel format_rational), never a lossy float.
		valStr, err := aletheia.FormatRational(v.Value)
		if err != nil {
			return die(err.Error())
		}
		fmt.Printf("  %-20s = %s%s\n", string(v.Name), valStr, unit)
	}
	if len(res.Errors) > 0 {
		fmt.Println("\nErrors:")
		for _, e := range res.Errors {
			fmt.Printf("  %s: %s\n", string(e.Name), e.Error)
		}
	}
	if len(res.Absent) > 0 {
		names := make([]string, 0, len(res.Absent))
		for _, a := range res.Absent {
			names = append(names, string(a))
		}
		fmt.Printf("Absent: %s\n", strings.Join(names, ", "))
	}
	return exitOK
}

// rationalJSON renders an extracted Rational for the --json output, matching the
// other bindings' CLIs (Python's FractionJSONEncoder): a bare integer when the
// denominator is 1, else a {"numerator","denominator"} object.  Extracted values
// are exact rationals (the kernel sends numerator/denominator), so this preserves
// that exactness on the wire instead of collapsing to a lossy float.
func rationalJSON(r aletheia.Rational) any {
	if r.Denominator == 1 {
		return r.Numerator
	}
	return map[string]int64{"numerator": r.Numerator, "denominator": r.Denominator}
}

// --- signals --------------------------------------------------------------

func cmdSignals(argv []string) int {
	fs := newFlagSet("signals")
	dbc := fs.String("dbc", "", ".dbc file")
	asJSON := fs.Bool("json", false, "output as JSON")
	if err := fs.Parse(argv); err != nil {
		return exitError
	}
	client, err := newClient()
	if err != nil {
		return die(err.Error())
	}
	def, err := loadDBCText(client, *dbc)
	if err != nil {
		return die(err.Error())
	}
	if *asJSON {
		return emitJSON(def) // canonical via DBCDefinition.MarshalJSON
	}
	total := 0
	for _, msg := range def.Messages {
		fmt.Printf("Message 0x%X %s (DLC %d)\n", msg.ID.Value(), msg.Name, msg.DLC.ToBytes())
		for _, sig := range msg.Signals {
			total++
			order := "BE"
			if sig.ByteOrder == aletheia.LittleEndian {
				order = "LE"
			}
			sign := "unsigned"
			if sig.IsSigned {
				sign = "signed"
			}
			// Exact rational render (kernel format_rational), never a lossy float.
			// Offset keeps the readable "+offset" form for non-negatives.
			factorStr, ferr := aletheia.FormatRational(sig.Factor)
			if ferr != nil {
				return die(ferr.Error())
			}
			offsetStr, oerr := aletheia.FormatRational(sig.Offset)
			if oerr != nil {
				return die(oerr.Error())
			}
			if sig.Offset.Numerator >= 0 {
				offsetStr = "+" + offsetStr
			}
			fmt.Printf("  %-20s bits[%d:%d] %s %-8s x%s %s %s\n",
				string(sig.Name), uint16(sig.StartBit), uint8(sig.BitLength),
				order, sign, factorStr, offsetStr, string(sig.Unit))
		}
	}
	fmt.Printf("\n%d messages, %d signals\n", len(def.Messages), total)
	return exitOK
}

// --- format-dbc -----------------------------------------------------------

func cmdFormatDBC(argv []string) int {
	fs := newFlagSet("format-dbc")
	dbc := fs.String("dbc", "", ".dbc file")
	if err := fs.Parse(argv); err != nil {
		return exitError
	}
	client, err := newClient()
	if err != nil {
		return die(err.Error())
	}
	def, err := loadDBCText(client, *dbc)
	if err != nil {
		return die(err.Error())
	}
	if _, err := client.ParseDBC(context.Background(), def); err != nil {
		return die(err.Error())
	}
	canonical, err := client.FormatDBC(context.Background())
	if err != nil {
		return die(err.Error())
	}
	return emitJSON(canonical) // canonical via DBCDefinition.MarshalJSON
}

// --- mux-query ------------------------------------------------------------

func cmdMuxQuery(argv []string) int {
	fs := newFlagSet("mux-query")
	dbc := fs.String("dbc", "", ".dbc file")
	extended := fs.Bool("extended", false, "treat CAN ID as 29-bit extended")
	muxName := fs.String("mux", "", "multiplexor signal name (with --value)")
	value := fs.Int("value", -1, "multiplexor value (with --mux)")
	asJSON := fs.Bool("json", false, "output as JSON")
	if err := fs.Parse(reorderArgs(argv, map[string]bool{"extended": true, "json": true})); err != nil {
		return exitError
	}
	if fs.NArg() != 1 {
		return die("mux-query requires a <message> positional argument (CAN ID or name)")
	}
	client, err := newClient()
	if err != nil {
		return die(err.Error())
	}
	def, err := loadDBCText(client, *dbc)
	if err != nil {
		return die(err.Error())
	}
	msg := resolveMuxMessage(def, fs.Arg(0), *extended)
	if msg == nil {
		return die(fmt.Sprintf("message not found by id or name: %q", fs.Arg(0)))
	}
	if (*muxName == "") != (*value < 0) {
		return die("--mux and --value must be provided together")
	}
	if *muxName != "" {
		sigs := msg.SignalsForMuxValue(aletheia.SignalName(*muxName), aletheia.MultiplexValue(*value))
		names := signalNames(sigs)
		if *asJSON {
			return emitJSON(map[string]any{
				"message_id":   msg.ID.Value(),
				"message_name": string(msg.Name),
				"multiplexor":  *muxName,
				"value":        *value,
				"signals":      names,
			})
		}
		fmt.Printf("Message 0x%X %s — %s = %d: %d signals (%s)\n",
			msg.ID.Value(), msg.Name, *muxName, *value, len(names), strings.Join(names, ", "))
		return exitOK
	}
	if *asJSON {
		muxes := make([]map[string]any, 0)
		for _, name := range msg.MultiplexorNames() {
			vals := make([]map[string]any, 0)
			for _, v := range msg.MultiplexValues(name) {
				vals = append(vals, map[string]any{
					"value":   uint32(v),
					"signals": signalNames(msg.SignalsForMuxValue(name, v)),
				})
			}
			muxes = append(muxes, map[string]any{"name": string(name), "values": vals})
		}
		return emitJSON(map[string]any{
			"message_id":     msg.ID.Value(),
			"message_name":   string(msg.Name),
			"is_multiplexed": msg.IsMultiplexed(),
			"multiplexors":   muxes,
		})
	}
	fmt.Printf("Message 0x%X %s (DLC %d)\n", msg.ID.Value(), msg.Name, msg.DLC.ToBytes())
	if !msg.IsMultiplexed() {
		fmt.Printf("  Not multiplexed — %d signals always present.\n", len(msg.Signals))
		return exitOK
	}
	for _, name := range msg.MultiplexorNames() {
		fmt.Printf("  %s:\n", string(name))
		for _, v := range msg.MultiplexValues(name) {
			names := signalNames(msg.SignalsForMuxValue(name, v))
			fmt.Printf("    value %d: %d signals (%s)\n", uint32(v), len(names), strings.Join(names, ", "))
		}
	}
	return exitOK
}

func resolveMuxMessage(def aletheia.DBCDefinition, ident string, extended bool) *aletheia.DBCMessage {
	if canID, err := parseCANID(ident); err == nil {
		if id, idErr := makeCANID(canID, extended); idErr == nil {
			if msg := def.MessageByID(id); msg != nil {
				return msg
			}
		}
	}
	return def.MessageByName(aletheia.MessageName(ident))
}

func signalNames(sigs []aletheia.DBCSignal) []string {
	names := make([]string, 0, len(sigs))
	for _, s := range sigs {
		names = append(names, string(s.Name))
	}
	return names
}
