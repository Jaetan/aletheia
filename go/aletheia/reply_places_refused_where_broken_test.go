//go:build cgo && linux

// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

// Every reply reader accepts a broken place of a real reply or refuses it in
// the one form. Each case's reply is the real kernel's answer to a command;
// every place of it is broken in turn, its key deleted, its value replaced by
// another JSON kind, or an array's entry so replaced, and each broken copy is
// fed to the reader of that reply, which accepts it or refuses it as
// "reply <path>: expected <what>, got <what came>" naming the broken place.
// The cases and the breaks are those of the Python binding's
// test_reply_places_refused_where_broken.py.

package aletheia

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"maps"
	"os"
	"path/filepath"
	"regexp"
	"slices"
	"strings"
	"testing"
)

// The reader of a kernel reply, named by the command whose reply it reads.
const (
	readerParseDBC      = "parseDBC"
	readerFormatDBC     = "formatDBC"
	readerFormatDBCText = "formatDBCText"
	readerValidateDBC   = "validateDBC"
	readerFrame         = "frame"
	readerEndStream     = "endStream"
	readerExtraction    = "extractAllSignals"
	readerEnvelope      = "error envelope"
)

// How a place is broken: its key deleted, its value or an array's entry
// replaced by another kind.
const (
	breakDeleted      = "deleted"
	breakRetyped      = "retyped"
	breakEntryRetyped = "entry retyped"
)

// The scenarios a real reply comes from, beside the corpus and the envelopes.
const (
	breakKitchenSink   = "kitchen_sink"
	breakUnknownTarget = "value_tables with an unknown VAL_ target"
	breakTwin          = "kitchen_sink with a twin message"
	breakProperties    = "kitchen_sink with five properties"
	breakMixed         = "a value, an over-range error and an absent signal"
)

// breakCorpus names the corpus DBCs every load case reads.
var breakCorpus = []string{
	breakKitchenSink,
	"attributes",
	"comments_groups",
	"env_vars",
	"value_tables",
	"multiplexing",
	"extended_can",
}

// breakEnvelope is one refused load: its fixture, the code its envelope
// carries, and the kitchen_sink text the kernel refuses.
type breakEnvelope struct {
	fixture string
	code    string
	text    func(base string) string
}

// breakEnvelopes are four kitchen_sink variants, each refused with its code.
var breakEnvelopes = []breakEnvelope{
	{"trailing input", CodeTextTrailingInput, func(base string) string { return base + "\nBO_ 1 X: 8\n" }},
	{"invalid character", CodeDBCInvalidCharacter, func(base string) string { return base + "\nCM_ \"a\"\"b\";\n" }},
	{"identifier past its bound", CodeInputBoundExceeded, func(base string) string {
		return strings.Replace(base, "BU_: ", "BU_: "+strings.Repeat("N", 129)+" ", 1)
	}},
	{"validation failed", CodeHandlerValidationFailed, func(base string) string {
		return base + "\nBO_ 256 Twin: 8 Engine\n SG_ D : 0|8@1+ (1,0) [0|255] \"\" Gateway\n"
	}},
}

// breakCase is a reader and the real reply it is fed broken copies of.
type breakCase struct {
	reader  string
	fixture string
}

// breakCases is every case: each load and its formatted DBC, the text
// formatter and the validator on kitchen_sink and its twin, a frame's batch,
// the end of that stream, an extraction, and four refused loads.
func breakCases() []breakCase {
	loads := append(slices.Clone(breakCorpus), breakUnknownTarget)
	var cases []breakCase
	for _, reader := range []string{readerParseDBC, readerFormatDBC} {
		for _, fixture := range loads {
			cases = append(cases, breakCase{reader, fixture})
		}
	}
	cases = append(cases,
		breakCase{readerFormatDBCText, breakKitchenSink},
		breakCase{readerFormatDBCText, breakTwin},
		breakCase{readerValidateDBC, breakKitchenSink},
		breakCase{readerValidateDBC, breakTwin},
		breakCase{readerFrame, breakProperties},
		breakCase{readerEndStream, breakProperties},
		breakCase{readerExtraction, breakMixed},
	)
	for _, e := range breakEnvelopes {
		cases = append(cases, breakCase{readerEnvelope, e.fixture})
	}
	return cases
}

// breakMixedText's message 256 holds a selector, a halved value, a signal its
// selector leaves out and one whose value's numerator passes the wire's
// 128-bit bound.
const breakMixedText = "VERSION \"\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\nBO_ 256 Mixed: 8 ECU\n" +
	" SG_ Mode M : 0|4@1+ (1,0) [0|15] \"\" Vector__XXX\n" +
	" SG_ Half m0 : 8|8@1+ (0.5,0) [0|127.5] \"\" Vector__XXX\n" +
	" SG_ Other m1 : 8|8@1+ (1,0) [0|255] \"\" Vector__XXX\n" +
	" SG_ Big : 16|17@1+ (0.12345678901234567890123456789012345678,0)" +
	" [0|10000] \"\" Vector__XXX\n"

// breakMixedFrame is Mode 0, Half 3/2, Big all ones over its low 16 bits.
var breakMixedFrame = []byte{0x00, 0x03, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00}

// Speed 250 rpm and Temp 60 degC, then Speed 0: Temp holds, Speed under 100
// fails.
var (
	breakFirstFrame  = []byte{0xE8, 0x03, 100, 0, 0, 0, 0, 0}
	breakSecondFrame = []byte{0x00, 0x00, 100, 0, 0, 0, 0, 0}
)

// breakCorpusText reads a corpus DBC's text.
func breakCorpusText(t *testing.T, name string) string {
	t.Helper()
	text, err := os.ReadFile(filepath.Join(repoRoot(t), "python", "tests", "fixtures", "dbc_corpus", name+".dbc"))
	if err != nil {
		t.Fatal(err)
	}
	return string(text)
}

// breakSession runs scenario on one kernel session of the real library,
// closed when the scenario ends.
func breakSession(t *testing.T, scenario func(c *Client)) {
	t.Helper()
	c := newFFIClient(t)
	defer func() { _ = c.Close() }()
	scenario(c)
}

// breakDecode decodes a reply, which the kernel writes as one JSON object,
// every number kept as its digits.
func breakDecode(t *testing.T, raw string, err error) map[string]any {
	t.Helper()
	if err != nil {
		t.Fatal(err)
	}
	dec := json.NewDecoder(strings.NewReader(raw))
	dec.UseNumber()
	var v map[string]any
	if err := dec.Decode(&v); err != nil {
		t.Fatalf("a reply that is not one JSON object: %v: %s", err, raw)
	}
	return v
}

// breakEncode writes a value as JSON text, every character as it is.
func breakEncode(t *testing.T, v any) string {
	t.Helper()
	var b bytes.Buffer
	enc := json.NewEncoder(&b)
	enc.SetEscapeHTML(false)
	if err := enc.Encode(v); err != nil {
		t.Fatal(err)
	}
	return strings.TrimSuffix(b.String(), "\n")
}

// breakCommand sends a JSON command and decodes the kernel's reply.
func breakCommand(t *testing.T, c *Client, command string, fields map[string]any) map[string]any {
	t.Helper()
	m := map[string]any{"type": "command", "command": command}
	maps.Copy(m, fields)
	raw, err := c.backend.Process(c.state, breakEncode(t, m))
	return breakDecode(t, raw, err)
}

// breakLoad loads a DBC text and answers the kernel's parseDBCText reply.
func breakLoad(t *testing.T, c *Client, text string) map[string]any {
	t.Helper()
	return breakCommand(t, c, "parseDBCText", map[string]any{"text": text})
}

// breakRequire holds that a reply's key holds the word given.
func breakRequire(t *testing.T, reply map[string]any, key, want string) {
	t.Helper()
	if got := reply[key]; got != want {
		t.Fatalf("reply %s: %v, want %q: %v", key, got, want, reply)
	}
}

// breakWithTwin appends a copy of the DBC's first message under another name,
// sharing its id.
func breakWithTwin(t *testing.T, dbc any) map[string]any {
	t.Helper()
	body, ok := dbc.(map[string]any)
	if !ok {
		t.Fatalf("a DBC that is not an object: %v", dbc)
	}
	messages, ok := body["messages"].([]any)
	if !ok || len(messages) == 0 {
		t.Fatalf("a DBC without messages: %v", body)
	}
	first, ok := messages[0].(map[string]any)
	if !ok {
		t.Fatalf("a message that is not an object: %v", messages[0])
	}
	twin := maps.Clone(first)
	twin["name"] = "Twin"
	out := maps.Clone(body)
	out["messages"] = append(slices.Clone(messages), twin)
	return out
}

// breakStandardFrame is the standard identifier 256 at the eight-byte length.
func breakStandardFrame(t *testing.T) (StandardID, DLC) {
	t.Helper()
	id, err := NewStandardID(256)
	if err != nil {
		t.Fatal(err)
	}
	dlc, err := NewDLC(8)
	if err != nil {
		t.Fatal(err)
	}
	return id, dlc
}

// breakLoadReplies loads every corpus DBC and the variant with an unknown
// VAL_ target, then formats each back.
func breakLoadReplies(t *testing.T, replies map[breakCase]any) {
	t.Helper()
	texts := map[string]string{}
	for _, name := range breakCorpus {
		texts[name] = breakCorpusText(t, name)
	}
	texts[breakUnknownTarget] = breakCorpusText(t, "value_tables") + "\nVAL_ 999 Ghost 0 \"Zero\" ;\n"
	for _, name := range append(slices.Clone(breakCorpus), breakUnknownTarget) {
		text := texts[name]
		breakSession(t, func(c *Client) {
			replies[breakCase{readerParseDBC, name}] = breakLoad(t, c, text)
			raw, err := c.backend.FormatDBCBinary(c.state)
			replies[breakCase{readerFormatDBC, name}] = breakDecode(t, raw, err)
		})
	}
}

// breakDBCCommandReplies formats and validates kitchen_sink's DBC and its
// twin-message variant.
func breakDBCCommandReplies(t *testing.T, replies map[breakCase]any) {
	t.Helper()
	loaded, ok := replies[breakCase{readerParseDBC, breakKitchenSink}].(map[string]any)
	if !ok {
		t.Fatal("kitchen_sink's load reply is missing")
	}
	kitchenSink := loaded["dbc"]
	bodies := map[string]any{breakKitchenSink: kitchenSink, breakTwin: breakWithTwin(t, kitchenSink)}
	for _, name := range []string{breakKitchenSink, breakTwin} {
		body := bodies[name]
		breakSession(t, func(c *Client) {
			replies[breakCase{readerFormatDBCText, name}] = breakCommand(t, c, "formatDBCText", map[string]any{"dbc": body})
			replies[breakCase{readerValidateDBC, name}] = breakCommand(t, c, "validateDBC", map[string]any{"dbc": body})
		})
	}
}

// breakStreamReplies streams kitchen_sink under five properties: a batch on
// the first frame, then the end.
func breakStreamReplies(t *testing.T, replies map[breakCase]any) {
	t.Helper()
	above := func(signal string, v int64) Formula {
		return Eventually{Inner: Atomic{Predicate: GreaterThan{Signal: SignalName(signal), Value: IntRational(v)}}}
	}
	below := func(signal string, v int64) Formula {
		return Always{Inner: Atomic{Predicate: LessThan{Signal: SignalName(signal), Value: IntRational(v)}}}
	}
	formulas := []Formula{above("Temp", 0), below("Speed", 100), above("Pressure", 10), below("Pressure", 100), above("Speed", 5000)}
	properties := make([]any, 0, len(formulas))
	for _, f := range formulas {
		properties = append(properties, must(serializeFormula(f)))
	}
	id, dlc := breakStandardFrame(t)
	breakSession(t, func(c *Client) {
		breakRequire(t, breakLoad(t, c, breakCorpusText(t, breakKitchenSink)), "status", "success")
		breakRequire(t, breakCommand(t, c, "setProperties", map[string]any{"properties": properties}), "status", "success")
		if _, err := c.backend.StartStreamBinary(c.state); err != nil {
			t.Fatal(err)
		}
		raw, err := c.backend.SendFrameBinary(c.state, Timestamp{Microseconds: 1000}, id, dlc, breakFirstFrame, nil, nil)
		first := breakDecode(t, raw, err)
		breakRequire(t, first, "type", "property_batch")
		raw, err = c.backend.SendFrameBinary(c.state, Timestamp{Microseconds: 2000}, id, dlc, breakSecondFrame, nil, nil)
		_ = breakDecode(t, raw, err)
		raw, err = c.backend.EndStreamBinary(c.state)
		replies[breakCase{readerFrame, breakProperties}] = first
		replies[breakCase{readerEndStream, breakProperties}] = breakDecode(t, raw, err)
	})
}

// breakExtractionReply extracts message 256 of the mixed DBC through the
// JSON-answering entry.
func breakExtractionReply(t *testing.T, replies map[breakCase]any) {
	t.Helper()
	id, dlc := breakStandardFrame(t)
	breakSession(t, func(c *Client) {
		breakRequire(t, breakLoad(t, c, breakMixedText), "status", "success")
		raw, err := c.backend.ExtractSignalsBinary(c.state, id, dlc, breakMixedFrame)
		replies[breakCase{readerExtraction, breakMixed}] = breakDecode(t, raw, err)
	})
}

// breakEnvelopeReplies refuses the four kitchen_sink variants, each with the
// code its fixture names.
func breakEnvelopeReplies(t *testing.T, replies map[breakCase]any) {
	t.Helper()
	base := breakCorpusText(t, breakKitchenSink)
	for _, e := range breakEnvelopes {
		breakSession(t, func(c *Client) {
			reply := breakLoad(t, c, e.text(base))
			breakRequire(t, reply, "code", e.code)
			replies[breakCase{readerEnvelope, e.fixture}] = reply
		})
	}
}

// breakKernelReplies answers every case's command on the real kernel.
func breakKernelReplies(t *testing.T) map[breakCase]any {
	t.Helper()
	replies := map[breakCase]any{}
	breakLoadReplies(t, replies)
	breakDBCCommandReplies(t, replies)
	breakStreamReplies(t, replies)
	breakExtractionReply(t, replies)
	breakEnvelopeReplies(t, replies)
	cases := breakCases()
	for _, c := range cases {
		if _, ok := replies[c]; !ok {
			t.Fatalf("no reply for %s on %s", c.reader, c.fixture)
		}
	}
	if len(replies) != len(cases) {
		t.Fatalf("%d replies for %d cases", len(replies), len(cases))
	}
	return replies
}

// replyBreak is one broken copy: the place, the value's steps from the root
// (a key, or an entry's position), how it is broken and what replaces it.
type replyBreak struct {
	path        replyPath
	where       []any
	breakage    string
	replacement any
}

// isWireRational tells the kernel's {numerator, denominator} object, a leaf
// of the reply proof.
func isWireRational(v any) bool {
	m, ok := v.(map[string]any)
	if !ok || len(m) != 2 {
		return false
	}
	_, numerator := m["numerator"]
	_, denominator := m["denominator"]
	return numerator && denominator
}

// breakStandIns names a value's replacements: "x" for a number, 0 for the
// rest, both for a rational.
func breakStandIns(v any) []any {
	zero := json.Number("0")
	if isWireRational(v) {
		return []any{zero, "x"}
	}
	if _, number := v.(json.Number); number {
		return []any{"x"}
	}
	return []any{zero}
}

// replyBreaks breaks every place below v: each key deleted and retyped, each
// entry retyped, keys taken in their sorted order.
func replyBreaks(v any, path replyPath, where []any) []replyBreak {
	var out []replyBreak
	switch x := v.(type) {
	case map[string]any:
		if isWireRational(x) {
			return nil
		}
		for _, key := range slices.Sorted(maps.Keys(x)) {
			here, steps := path.at(key), append(slices.Clone(where), key)
			out = append(out, replyBreak{here, steps, breakDeleted, nil})
			for _, stand := range breakStandIns(x[key]) {
				out = append(out, replyBreak{here, steps, breakRetyped, stand})
			}
			out = append(out, replyBreaks(x[key], here, steps)...)
		}
	case []any:
		for index, entry := range x {
			steps := append(slices.Clone(where), index)
			for _, stand := range breakStandIns(entry) {
				out = append(out, replyBreak{path, steps, breakEntryRetyped, stand})
			}
			out = append(out, replyBreaks(entry, path, steps)...)
		}
	}
	return out
}

// brokenCopy copies v with the place at where broken as change says, sharing
// the rest.
func brokenCopy(v any, where []any, change replyBreak) any {
	step, rest := where[0], where[1:]
	switch x := v.(type) {
	case map[string]any:
		key := step.(string)
		out := maps.Clone(x)
		switch {
		case len(rest) > 0:
			out[key] = brokenCopy(x[key], rest, change)
		case change.breakage == breakDeleted:
			delete(out, key)
		default:
			out[key] = change.replacement
		}
		return out
	case []any:
		index := step.(int)
		out := slices.Clone(x)
		if len(rest) > 0 {
			out[index] = brokenCopy(x[index], rest, change)
		} else {
			out[index] = change.replacement
		}
		return out
	}
	panic(fmt.Sprintf("a step %v below a value that is neither an object nor an array", step))
}

// breakArrival names what came at the broken place: nothing for a deleted
// key, else its kind.
func breakArrival(change replyBreak) string {
	if change.breakage == breakDeleted {
		return cameNothing
	}
	return jsonKind(change.replacement)
}

// breakSpelled spells a value's steps as dbc.messages[0].signals[1].factor.
func breakSpelled(where []any) string {
	var b strings.Builder
	for _, step := range where {
		if index, ok := step.(int); ok {
			fmt.Fprintf(&b, "[%d]", index)
		} else {
			fmt.Fprintf(&b, ".%s", step)
		}
	}
	return strings.TrimPrefix(b.String(), ".")
}

// readBrokenReply feeds raw to the reader of the case's reply, the one the
// client applies to the command's answer; an error envelope is read by the
// reader every command's error status reaches.
func readBrokenReply(reader, raw string) error {
	var err error
	switch reader {
	case readerParseDBC:
		_, err = parseParsedDBCResponse(raw)
	case readerFormatDBC:
		_, err = parseDBCResponse(raw)
	case readerFormatDBCText:
		_, err = parseDBCTextResponse(raw)
	case readerValidateDBC:
		_, err = parseValidationResponse(raw)
	case readerFrame:
		_, err = parseFrameResponse(raw)
	case readerEndStream:
		_, err = parseStreamResponse(raw)
	case readerExtraction:
		_, err = parseExtractionResponse(raw)
	case readerEnvelope:
		m, perr := parseResponse(raw)
		if perr != nil {
			return perr
		}
		err = checkErrorStatus(m)
	default:
		panic("no reader named " + reader)
	}
	return err
}

// isReplyRefusal tells a reply reader's refusal: a protocol error with no
// code.
func isReplyRefusal(err error) bool {
	var e *Error
	return errors.As(err, &e) && e.Kind == ErrProtocol && e.Code == ""
}

// breakVerdict says how the case's reader took a broken copy: "" for an
// acceptance or the one form naming the broken place. An error envelope's
// reader accepts by answering the error the envelope carries.
func breakVerdict(c breakCase, change replyBreak, raw string) (verdict string) {
	defer func() {
		if r := recover(); r != nil {
			verdict = fmt.Sprintf("crashed with %v", r)
		}
	}()
	err := readBrokenReply(c.reader, raw)
	switch {
	case err == nil:
		return ""
	case isReplyRefusal(err):
		text := err.Error()
		head, tail := fmt.Sprintf("reply %s: expected ", change.path), ", got "+breakArrival(change)
		if strings.HasPrefix(text, head) && strings.HasSuffix(text, tail) {
			return ""
		}
		return fmt.Sprintf("refused as %q", text)
	case c.reader == readerEnvelope:
		return ""
	default:
		return fmt.Sprintf("answered %T: %v", err, err)
	}
}

// breakFailure is a broken place a reader neither accepted nor refused in the
// one form.
type breakFailure struct {
	path     replyPath
	breakage string
	verdict  string
}

// A reader accepts each broken place of a real reply or refuses it as
// "reply <path>: expected ..., got ..." naming the place.
func TestABrokenReplyPlaceIsAcceptedOrRefusedInTheOneForm(t *testing.T) {
	replies := breakKernelReplies(t)
	copies := 0
	for _, c := range breakCases() {
		reply := replies[c]
		breaks := replyBreaks(reply, "", nil)
		copies += len(breaks)
		t.Run(c.reader+"-"+c.fixture, func(t *testing.T) {
			var order []breakFailure
			wheres := map[breakFailure][][]any{}
			for _, change := range breaks {
				raw := breakEncode(t, brokenCopy(reply, change.where, change))
				if verdict := breakVerdict(c, change, raw); verdict != "" {
					failure := breakFailure{change.path, change.breakage, verdict}
					if _, seen := wheres[failure]; !seen {
						order = append(order, failure)
					}
					wheres[failure] = append(wheres[failure], change.where)
				}
			}
			if len(order) == 0 {
				return
			}
			lines := make([]string, 0, len(order))
			out := 0
			for _, failure := range order {
				out += len(wheres[failure])
				lines = append(lines, fmt.Sprintf("%s %s (at %s, x%d): %s",
					failure.path, failure.breakage, breakSpelled(wheres[failure][0]), len(wheres[failure]), failure.verdict))
			}
			t.Errorf("%s on %s: %d broken copies out of the one form, %d by path, breakage and verdict\n%s",
				c.reader, c.fixture, out, len(lines), strings.Join(lines, "\n"))
		})
	}
	t.Logf("%d broken copies over %d cases", copies, len(breakCases()))
}

// The reply proof's clauses: a table, then its path as keys before [].
var (
	proofClause      = regexp.MustCompile(`^(replyRange|replyText|replyNonEmpty) \(((?:"[^"]*" ∷ )+)\[\]\)`)
	proofClauseStart = regexp.MustCompile(`^(?:replyRange|replyText|replyNonEmpty) \(`)
	proofKey         = regexp.MustCompile(`"([^"]*)"`)
)

// proofPaths reads the paths of the reply proof's replyRange, replyText and
// replyNonEmpty tables.
func proofPaths(t *testing.T) map[string]map[replyPath]bool {
	t.Helper()
	source, err := os.ReadFile(filepath.Join(repoRoot(t), "src", "Aletheia", "Protocol", "ReplyRange.agda"))
	if err != nil {
		t.Fatal(err)
	}
	tables := map[string]map[replyPath]bool{}
	for line := range strings.Lines(string(source)) {
		if !proofClauseStart.MatchString(line) {
			continue
		}
		clause := proofClause.FindStringSubmatch(line)
		if clause == nil {
			t.Fatalf("a clause the test cannot read: %s", line)
		}
		var keys []string
		for _, key := range proofKey.FindAllStringSubmatch(clause[2], -1) {
			keys = append(keys, key[1])
		}
		if tables[clause[1]] == nil {
			tables[clause[1]] = map[replyPath]bool{}
		}
		tables[clause[1]][replyPath(strings.Join(keys, "/"))] = true
	}
	return tables
}

// Each path of the reply proof's three tables is broken in some case's reply.
func TestEveryPlaceTheReplyProofNamesIsBrokenBySomeCase(t *testing.T) {
	tables := proofPaths(t)
	if got := slices.Sorted(maps.Keys(tables)); !slices.Equal(got, []string{"replyNonEmpty", "replyRange", "replyText"}) {
		t.Fatalf("the reply proof's tables: %v", got)
	}
	replies := breakKernelReplies(t)
	broken := map[replyPath]bool{}
	for _, c := range breakCases() {
		for _, change := range replyBreaks(replies[c], "", nil) {
			broken[change.path] = true
		}
	}
	for _, table := range slices.Sorted(maps.Keys(tables)) {
		var unbroken []string
		for path := range tables[table] {
			if !broken[path] {
				unbroken = append(unbroken, string(path))
			}
		}
		slices.Sort(unbroken)
		t.Logf("%s: %d of %d paths broken", table, len(tables[table])-len(unbroken), len(tables[table]))
		if len(unbroken) > 0 {
			t.Errorf("%s paths no case breaks: %v", table, unbroken)
		}
	}
}
