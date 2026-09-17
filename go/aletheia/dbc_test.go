// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia_test

import (
	"bytes"
	"errors"
	"strings"
	"testing"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

// mockClient is a client over a mock holding the given responses, closed when
// the test ends.
func mockClient(t *testing.T, responses ...aletheia.MockResponse) (*aletheia.Client, *aletheia.MockBackend) {
	t.Helper()
	mock := aletheia.NewMockBackend(responses...)
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { _ = c.Close() })
	return c, mock
}

// parsedClient is a mock client that has loaded testDBC, so the signal index
// is populated; the responses follow the parse.
func parsedClient(t *testing.T, responses ...aletheia.MockResponse) (*aletheia.Client, *aletheia.MockBackend) {
	t.Helper()
	c, mock := mockClient(t, append([]aletheia.MockResponse{aletheia.RespondParseDBC(testDBC())}, responses...)...)
	if _, err := c.ParseDBC(ctx, testDBC()); err != nil {
		t.Fatal(err)
	}
	return c, mock
}

// requireKind asserts err is an *aletheia.Error of the kind.
func requireKind(t *testing.T, err error, kind aletheia.ErrorKind) {
	t.Helper()
	if err == nil {
		t.Fatal("expected an error, got nil")
	}
	var aErr *aletheia.Error
	if !errors.As(err, &aErr) {
		t.Fatalf("expected *aletheia.Error, got %T: %v", err, err)
	}
	if aErr.Kind != kind {
		t.Errorf("kind: got %s, want %s: %v", aErr.Kind, kind, err)
	}
}

// formatDBCResponse is a success response to FormatDBC carrying one message.
func formatDBCResponse(message string) string {
	return `{"status":"success","dbc":{"version":"","messages":[` + message + `]}}`
}

// oneSignalMessage is a standard-ID message carrying one signal.
func oneSignalMessage(signal string) string {
	return `{"id":100,"extended":false,"name":"Msg","dlc":8,"sender":"ECU","signals":[` + signal + `]}`
}

const (
	sid123        = 0x123
	speedSignal   = `{"name":"Speed","startBit":0,"length":16,"byteOrder":"little_endian","signed":false,"factor":{"numerator":1,"denominator":10},"offset":0,"minimum":0,"maximum":300,"unit":"km/h","presence":"always"}`
	rpmSignal     = `{"name":"RPM","startBit":16,"length":16,"byteOrder":"little_endian","signed":false,"factor":1,"offset":0,"minimum":0,"maximum":8000,"unit":"rpm","presence":"always"}`
	zeroPayload8  = "\x00\x00\x00\x00\x00\x00\x00\x00"
	extractionRsp = `{"status":"success","values":[{"name":"Speed","value":{"numerator":241,"denominator":2}},{"name":"Ratio","value":{"numerator":1,"denominator":3}}],"errors":[{"name":"Broken","error":"bit extraction failed"}],"absent":["Temp"]}`
)

func standardID(t *testing.T, v uint16) aletheia.StandardID {
	t.Helper()
	sid, err := aletheia.NewStandardID(v)
	if err != nil {
		t.Fatal(err)
	}
	return sid
}

// ParseDBC serialises the definition the way the other bindings do: an
// always-present signal carries "presence":"always", a multiplexed one its
// multiplexor and values, and an extended ID its flag.
func TestParseDBC_SerialisesPresenceAndID(t *testing.T) {
	eid, _ := aletheia.NewExtendedID(0x18FEF100)
	dlc, _ := aletheia.NewDLC(8)
	rat := func(n int64) aletheia.Rational { return aletheia.IntRational(n) }
	muxDBC := aletheia.DBCDefinition{Messages: []aletheia.DBCMessage{{
		ID: standardID(t, 0x200), Name: "MuxMsg", DLC: dlc, Sender: "ECU",
		Signals: []aletheia.DBCSignal{
			{Name: "MuxSelector", StartBit: 0, BitLength: 8, ByteOrder: aletheia.LittleEndian, Presence: aletheia.AlwaysPresent{},
				Factor: rat(1), Offset: rat(0), Minimum: rat(0), Maximum: rat(3)},
			{Name: "TempA", StartBit: 8, BitLength: 16, ByteOrder: aletheia.LittleEndian,
				Presence: aletheia.Multiplexed{Multiplexor: "MuxSelector", MultiplexValues: []aletheia.MultiplexValue{0}},
				Factor:   aletheia.Rational{Numerator: 1, Denominator: 10}, Offset: rat(-40), Minimum: rat(-40), Maximum: rat(215), Unit: "degC"},
		},
	}}}
	extendedDBC := aletheia.DBCDefinition{Messages: []aletheia.DBCMessage{{ID: eid, Name: "J1939Msg", DLC: dlc, Sender: "Node"}}}
	cases := map[string]struct {
		dbc  aletheia.DBCDefinition
		want []string
	}{
		"always present": {testDBC(), []string{`"presence":"always"`}},
		"multiplexed":    {muxDBC, []string{`"presence":"multiplexed"`, `"multiplexor":"MuxSelector"`, `"multiplex_values":[0]`}},
		"extended id":    {extendedDBC, []string{`"extended":true`, `"id":419361024`}},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			c, mock := mockClient(t, aletheia.RespondParseDBC(tc.dbc))
			if _, err := c.ParseDBC(ctx, tc.dbc); err != nil {
				t.Fatalf("ParseDBC: %v", err)
			}
			inputs := mock.Inputs()
			if len(inputs) != 1 {
				t.Fatalf("expected 1 input, got %d", len(inputs))
			}
			for _, w := range tc.want {
				if !strings.Contains(inputs[0], w) {
					t.Errorf("serialized DBC lacks %s: %s", w, inputs[0])
				}
			}
		})
	}
}

func TestValidateDBC_NoErrors(t *testing.T) {
	c, _ := mockClient(t, aletheia.Respond(`{"status":"validation","has_errors":false,"issues":[]}`))
	result, err := c.ValidateDBC(ctx, testDBC())
	if err != nil {
		t.Fatalf("ValidateDBC: %v", err)
	}
	if result.HasErrors || len(result.Issues) != 0 {
		t.Errorf("expected no issues, got has_errors=%v issues=%v", result.HasErrors, result.Issues)
	}
}

func TestValidateDBC_WithIssues(t *testing.T) {
	c, _ := mockClient(t, aletheia.Respond(`{"status":"validation","has_errors":true,"issues":[
		{"severity":"error","code":"factor_zero","detail":"Signal Speed has zero factor"},
		{"severity":"warning","code":"empty_message","detail":"Message Diag has no signals"}]}`))
	result, err := c.ValidateDBC(ctx, testDBC())
	if err != nil {
		t.Fatalf("ValidateDBC: %v", err)
	}
	if !result.HasErrors {
		t.Error("expected has_errors=true")
	}
	if len(result.Issues) != 2 {
		t.Fatalf("expected 2 issues, got %d", len(result.Issues))
	}
	if result.Issues[0].Code != aletheia.IssueFactorZero || result.Issues[0].Severity != aletheia.SeverityError {
		t.Errorf("issue 0: got %s %s, want factor_zero error", result.Issues[0].Code, result.Issues[0].Severity)
	}
	if result.Issues[1].Severity != aletheia.SeverityWarning {
		t.Errorf("issue 1: got %s, want warning", result.Issues[1].Severity)
	}
}

func TestValidateDBC_UnknownSeverityRejected(t *testing.T) {
	c, _ := mockClient(t, aletheia.Respond(`{"status":"validation","has_errors":false,"issues":[{"severity":"info","code":"empty_message","detail":"x"}]}`))
	_, err := c.ValidateDBC(ctx, testDBC())
	requireKind(t, err, aletheia.ErrProtocol)
}

// FormatDBC decodes every field of the message and its signals.
func TestFormatDBC(t *testing.T) {
	c, _ := mockClient(t, aletheia.Respond(`{"status":"success","dbc":{"version":"2.0","messages":[
		{"id":291,"extended":false,"name":"EngineData","dlc":8,"sender":"ECU","signals":[`+speedSignal+`,`+rpmSignal+`]}]}}`))
	dbc, err := c.FormatDBC(ctx)
	if err != nil {
		t.Fatalf("FormatDBC: %v", err)
	}
	if dbc.Version != "2.0" {
		t.Errorf("version: got %q, want %q", dbc.Version, "2.0")
	}
	if len(dbc.Messages) != 1 {
		t.Fatalf("messages: got %d, want 1", len(dbc.Messages))
	}
	msg := dbc.Messages[0]
	if msg.Name != "EngineData" || msg.ID.Value() != 291 || msg.ID.IsExtended() || msg.DLC.Value() != 8 || msg.Sender != "ECU" {
		t.Errorf("message: got %+v, want EngineData 291 standard dlc 8 from ECU", msg)
	}
	if len(msg.Signals) != 2 {
		t.Fatalf("signals: got %d, want 2", len(msg.Signals))
	}
	speed := msg.Signals[0]
	if speed.Name != "Speed" || speed.StartBit != 0 || speed.BitLength != 16 || speed.ByteOrder != aletheia.LittleEndian ||
		speed.Factor != (aletheia.Rational{Numerator: 1, Denominator: 10}) || speed.Unit != "km/h" {
		t.Errorf("signal 0: got %+v", speed)
	}
	if msg.Signals[1].Name != "RPM" {
		t.Errorf("signal 1 name: got %q, want RPM", msg.Signals[1].Name)
	}
}

// FormatDBC decodes an extended ID, a multiplexed presence, and a signal
// spanning the whole 64-byte CAN-FD frame, which the kernel allows and the
// decoder must not re-reject with a classic-CAN cap.
func TestFormatDBC_Shapes(t *testing.T) {
	t.Run("extended id", func(t *testing.T) {
		c, _ := mockClient(t, aletheia.Respond(formatDBCResponse(`{"id":419361024,"extended":true,"name":"J1939Msg","dlc":8,"sender":"Node","signals":[]}`)))
		dbc, err := c.FormatDBC(ctx)
		if err != nil {
			t.Fatalf("FormatDBC: %v", err)
		}
		if len(dbc.Messages) != 1 || !dbc.Messages[0].ID.IsExtended() || dbc.Messages[0].ID.Value() != 419361024 {
			t.Errorf("got %+v, want one extended message 419361024", dbc.Messages)
		}
	})
	t.Run("multiplexed", func(t *testing.T) {
		c, _ := mockClient(t, aletheia.Respond(formatDBCResponse(`{"id":512,"extended":false,"name":"MuxMsg","dlc":8,"sender":"ECU","signals":[
			{"name":"MuxSel","startBit":0,"length":8,"byteOrder":"little_endian","signed":false,"factor":1,"offset":0,"minimum":0,"maximum":3,"unit":"","presence":"always"},
			{"name":"TempA","startBit":8,"length":16,"byteOrder":"little_endian","signed":false,"factor":{"numerator":1,"denominator":10},"offset":-40,"minimum":-40,"maximum":215,"unit":"degC","presence":"multiplexed","multiplexor":"MuxSel","multiplex_values":[0]}]}`)))
		dbc, err := c.FormatDBC(ctx)
		if err != nil {
			t.Fatalf("FormatDBC: %v", err)
		}
		sigs := dbc.Messages[0].Signals
		if len(sigs) != 2 {
			t.Fatalf("expected 2 signals, got %d", len(sigs))
		}
		if _, ok := sigs[0].Presence.(aletheia.AlwaysPresent); !ok {
			t.Errorf("MuxSel: expected AlwaysPresent, got %T", sigs[0].Presence)
		}
		mux, ok := sigs[1].Presence.(aletheia.Multiplexed)
		if !ok || mux.Multiplexor != "MuxSel" || len(mux.MultiplexValues) != 1 || mux.MultiplexValues[0] != 0 {
			t.Errorf("TempA: expected Multiplexed by MuxSel on [0], got %+v", sigs[1].Presence)
		}
	})
	t.Run("full-frame FD signal", func(t *testing.T) {
		c, _ := mockClient(t, aletheia.Respond(formatDBCResponse(`{"id":100,"extended":false,"name":"Wide","dlc":64,"sender":"ECU","signals":[
			{"name":"Blob","startBit":0,"length":512,"byteOrder":"little_endian","signed":false,"factor":1,"offset":0,"minimum":0,"maximum":0,"unit":"","presence":"always"}]}`)))
		dbc, err := c.FormatDBC(ctx)
		if err != nil {
			t.Fatalf("FormatDBC: %v", err)
		}
		sig := dbc.Messages[0].Signals[0]
		if sig.StartBit != 0 || sig.BitLength != 512 {
			t.Errorf("got bits[%d:%d], want bits[0:512]", uint16(sig.StartBit), uint16(sig.BitLength))
		}
	})
}

// A FormatDBC response the decoder cannot trust is a protocol error, and
// where the decoder names the reason the message says so.
func TestFormatDBC_MalformedResponsesAreProtocolErrors(t *testing.T) {
	sig := func(fields string) string {
		return oneSignalMessage(`{` + fields + `}`)
	}
	const base = `"startBit":0,"length":8,"byteOrder":"little_endian","signed":false,"factor":1,"offset":0,"minimum":0,"maximum":255,"unit":""`
	cases := map[string]struct {
		message string
		want    string
	}{
		"invalid byte order":              {sig(`"name":"Sig",` + strings.Replace(base, "little_endian", "middle_endian", 1) + `,"presence":"always"`), ""},
		"negative id":                     {`{"id":-1,"extended":false,"name":"Msg","dlc":8,"sender":"ECU","signals":[]}`, ""},
		"missing signal name":             {sig(base + `,"presence":"always"`), ""},
		"start bit out of range":          {sig(`"name":"Sig",` + strings.Replace(base, `"startBit":0`, `"startBit":600`, 1) + `,"presence":"always"`), "out of range"},
		"length zero":                     {sig(`"name":"Sig",` + strings.Replace(base, `"length":8`, `"length":0`, 1) + `,"presence":"always"`), "out of range"},
		"length excessive":                {sig(`"name":"Sig",` + strings.Replace(base, `"length":8`, `"length":513`, 1) + `,"presence":"always"`), "out of range"},
		"unknown presence":                {sig(`"name":"Sig",` + base + `,"presence":"sometimes"`), "unknown signal presence"},
		"missing presence":                {sig(`"name":"Sig",` + base), ""},
		"multiplexed without multiplexor": {sig(`"name":"Sig",` + base + `,"presence":"multiplexed","multiplex_values":[0]`), ""},
		"multiplex value over u32":        {sig(`"name":"Sig",` + base + `,"presence":"multiplexed","multiplexor":"M","multiplex_values":[5000000000]`), ""},
		"non-boolean extended":            {`{"id":100,"extended":"true","name":"Msg","dlc":8,"sender":"ECU","signals":[]}`, ""},
		"empty message name":              {`{"id":100,"extended":false,"name":"","dlc":8,"sender":"ECU","signals":[]}`, ""},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			c, _ := mockClient(t, aletheia.Respond(formatDBCResponse(tc.message)))
			_, err := c.FormatDBC(ctx)
			requireKind(t, err, aletheia.ErrProtocol)
			if tc.want != "" {
				requireErrorContains(t, err, tc.want)
			}
		})
	}
}

// ExtractSignals carries exact rationals, the extraction errors and the
// absent signals; Get finds a value by name.
func TestExtractSignals(t *testing.T) {
	c, _ := mockClient(t, aletheia.Respond(extractionRsp))
	result, err := c.ExtractSignals(ctx, standardID(t, sid123), dlc8(), aletheia.FramePayload{0xDE, 0xAD, 0xBE, 0xEF, 0, 0, 0, 0})
	if err != nil {
		t.Fatalf("ExtractSignals: %v", err)
	}
	if len(result.Values) != 2 || result.Values[0].Name != "Speed" {
		t.Fatalf("values: got %+v", result.Values)
	}
	if v, ok := result.Get("Speed"); !ok || v != (aletheia.Rational{Numerator: 241, Denominator: 2}) {
		t.Errorf("Get(Speed) = %v %v, want 241/2", v, ok)
	}
	if v, ok := result.Get("Ratio"); !ok || v != (aletheia.Rational{Numerator: 1, Denominator: 3}) {
		t.Errorf("Get(Ratio) = %v %v, want the exact 1/3", v, ok)
	}
	if _, ok := result.Get("Nonexistent"); ok {
		t.Error("Get(Nonexistent) should report absence")
	}
	if len(result.Errors) != 1 || result.Errors[0].Name != "Broken" || result.Errors[0].Error != "bit extraction failed" {
		t.Errorf("errors: got %+v", result.Errors)
	}
	if len(result.Absent) != 1 || result.Absent[0] != "Temp" {
		t.Errorf("absent: got %v, want [Temp]", result.Absent)
	}
}

// An extraction response the decoder cannot trust is refused, as a protocol
// error where the decoder classifies it.
func TestExtractSignals_MalformedResponsesAreRefused(t *testing.T) {
	cases := map[string]struct {
		response string
		want     string
		kind     aletheia.ErrorKind
	}{
		"zero denominator":  {`{"status":"success","values":[{"name":"Bad","value":{"numerator":1,"denominator":0}}],"errors":[],"absent":[]}`, "", aletheia.ErrProtocol},
		"wrong status":      {`{"status":"validation","values":[],"errors":[],"absent":[]}`, "expected success", aletheia.ErrProtocol},
		"non-string absent": {`{"status":"success","values":[],"errors":[],"absent":[123]}`, "expected string in absent", aletheia.ErrProtocol},
		"empty signal name": {`{"status":"success","values":[{"name":"","value":42}],"errors":[],"absent":[]}`, "", aletheia.ErrProtocol},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			c, _ := mockClient(t, aletheia.Respond(tc.response))
			_, err := c.ExtractSignals(ctx, standardID(t, sid123), dlc8(), aletheia.FramePayload(zeroPayload8))
			requireKind(t, err, tc.kind)
			if tc.want != "" {
				requireErrorContains(t, err, tc.want)
			}
		})
	}
}

// BuildFrame returns the payload the backend built, whatever its length;
// a byte the wire cannot hold is refused.
func TestBuildFrame(t *testing.T) {
	speed := []aletheia.SignalValue{{Name: "Speed", Value: aletheia.Rational{Numerator: 241, Denominator: 2}}}
	t.Run("payload", func(t *testing.T) {
		c, _ := parsedClient(t, aletheia.Respond(`{"status":"success","data":[222,173,190,239,0,0,0,0]}`))
		payload, err := c.BuildFrame(ctx, standardID(t, sid123), dlc8(), speed)
		if err != nil {
			t.Fatalf("BuildFrame: %v", err)
		}
		if !bytes.Equal(payload, aletheia.FramePayload{0xDE, 0xAD, 0xBE, 0xEF, 0, 0, 0, 0}) {
			t.Errorf("got %v", payload)
		}
	})
	t.Run("shorter payload is returned as built", func(t *testing.T) {
		c, _ := parsedClient(t, aletheia.Respond(`{"status":"success","data":[1,2,3,4,5,6,7]}`))
		payload, err := c.BuildFrame(ctx, standardID(t, sid123), dlc8(), speed)
		if err != nil {
			t.Fatalf("BuildFrame: %v", err)
		}
		if !bytes.Equal(payload, aletheia.FramePayload{1, 2, 3, 4, 5, 6, 7}) {
			t.Errorf("got %v", payload)
		}
	})
	t.Run("byte out of range", func(t *testing.T) {
		c, _ := parsedClient(t, aletheia.Respond(`{"status":"success","data":[256,0,0,0,0,0,0,0]}`))
		_, err := c.BuildFrame(ctx, standardID(t, sid123), dlc8(), speed)
		requireErrorContains(t, err, "out of range")
	})
}

func TestUpdateFrame(t *testing.T) {
	c, _ := parsedClient(t, aletheia.Respond(`{"status":"success","data":[0,100,0,0,0,0,0,0]}`))
	payload, err := c.UpdateFrame(ctx, standardID(t, sid123), dlc8(), aletheia.FramePayload(zeroPayload8),
		[]aletheia.SignalValue{{Name: "Speed", Value: aletheia.IntRational(100)}})
	if err != nil {
		t.Fatalf("UpdateFrame: %v", err)
	}
	if payload[1] != 100 {
		t.Errorf("expected byte[1]=100, got %d", payload[1])
	}
}

// Each predicate serialises with its operator and fields under the names the
// wire uses.
func TestPredicatesSerialise(t *testing.T) {
	cases := map[string]struct {
		predicate aletheia.Predicate
		want      []string
	}{
		"changed by": {aletheia.ChangedBy{Signal: "RPM", Delta: aletheia.IntRational(500)}, []string{`"changedBy"`, `"delta"`}},
		"between":    {aletheia.Between{Signal: "Temp", Min: aletheia.IntRational(-40), Max: aletheia.IntRational(120)}, []string{`"between"`, `"min"`, `"max"`}},
	}
	for name, tc := range cases {
		t.Run(name, func(t *testing.T) {
			c, mock := mockClient(t, aletheia.Respond(`{"status":"success"}`))
			if err := c.SetProperties(ctx, []aletheia.Formula{aletheia.Atomic{Predicate: tc.predicate}}); err != nil {
				t.Fatalf("SetProperties: %v", err)
			}
			inputs := mock.Inputs()
			if len(inputs) != 1 {
				t.Fatalf("expected 1 input, got %d", len(inputs))
			}
			for _, w := range tc.want {
				if !strings.Contains(inputs[0], w) {
					t.Errorf("serialized property lacks %s: %s", w, inputs[0])
				}
			}
		})
	}
}

// A Between whose minimum exceeds its maximum is a validation error that
// renders both bounds as exact rationals, not as floats.
func TestBetween_MinExceedsMax(t *testing.T) {
	c, _ := mockClient(t)
	err := c.SetProperties(ctx, []aletheia.Formula{aletheia.Atomic{Predicate: aletheia.Between{
		Signal: "Temp", Min: aletheia.Rational{Numerator: 1, Denominator: 3}, Max: aletheia.IntRational(0)}}})
	requireKind(t, err, aletheia.ErrValidation)
	requireErrorContains(t, err, "min (1/3) exceeds max (0)")
}

func TestFormatDBC_AfterClose(t *testing.T) {
	c, err := aletheia.NewClient(aletheia.NewMockBackend())
	if err != nil {
		t.Fatal(err)
	}
	if err := c.Close(); err != nil {
		t.Fatal(err)
	}
	_, err = c.FormatDBC(ctx)
	requireKind(t, err, aletheia.ErrState)
}

// BuildFrame and UpdateFrame resolve signal names through the DBC the client
// has loaded; before any ParseDBC both are refused with a state error that
// says so, without reaching the backend.
func TestBuildFrame_BeforeParseDBC(t *testing.T) {
	c, mock := mockClient(t)
	signals := []aletheia.SignalValue{{Name: "Speed", Value: aletheia.IntRational(1)}}
	_, err := c.BuildFrame(ctx, standardID(t, 0x100), dlc8(), signals)
	requireErrorContains(t, err, "no DBC loaded")
	requireKind(t, err, aletheia.ErrState)
	_, err = c.UpdateFrame(ctx, standardID(t, 0x100), dlc8(), aletheia.FramePayload(zeroPayload8), signals)
	requireErrorContains(t, err, "no DBC loaded")
	if n := len(mock.Inputs()); n != 0 {
		t.Errorf("the backend was reached %d times before a DBC was loaded", n)
	}
}

// Once a DBC is loaded the client tries the binary extraction first. The
// MockBackend answers it with ErrBinaryPathUnsupported, and that error alone
// falls back to the JSON extraction, whose canned response is the result.
func TestExtractSignals_MockBinaryFallthrough(t *testing.T) {
	c, _ := parsedClient(t, aletheia.Respond(`{"status":"success","values":[{"name":"Speed","value":150}],"errors":[],"absent":[]}`))
	result, err := c.ExtractSignals(ctx, standardID(t, sid123), dlc8(), aletheia.FramePayload(zeroPayload8))
	if err != nil {
		t.Fatalf("ExtractSignals did not fall back: %v", err)
	}
	if len(result.Values) != 1 || result.Values[0].Name != "Speed" ||
		result.Values[0].Value != (aletheia.Rational{Numerator: 150, Denominator: 1}) {
		t.Errorf("expected Speed=150 through the JSON fallback, got %+v", result.Values)
	}
}
