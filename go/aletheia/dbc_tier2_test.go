package aletheia_test

import (
	"encoding/json"
	"strings"
	"testing"

	"github.com/aletheia-automotive/aletheia-go/aletheia"
)

// buildTier2Fixture assembles a DbcDefinition exercising every Tier 2
// variant (5 comment targets, 5 attr types, 5 attr values, 7 attr
// targets, 3 attribute sub-records) so serialize/parse coverage is
// exhaustive in a single round-trip.
func buildTier2Fixture(t *testing.T) aletheia.DbcDefinition {
	t.Helper()
	id, err := aletheia.NewStandardID(256)
	if err != nil {
		t.Fatal(err)
	}
	dlc, err := aletheia.BytesToDLC(8)
	if err != nil {
		t.Fatal(err)
	}
	msg := aletheia.NewDbcMessage(id, "EngineData", dlc, "ECU", nil, nil)

	return aletheia.DbcDefinition{
		Version:  "1.0",
		Messages: []aletheia.DbcMessage{msg},
		Nodes: []aletheia.DbcNode{
			{Name: "ECU"},
			{Name: "Gateway"},
		},
		Comments: []aletheia.DbcComment{
			{Target: aletheia.DbcCommentTargetNetwork{}, Text: "network scope"},
			{Target: aletheia.DbcCommentTargetNode{Node: "ECU"}, Text: "node scope"},
			{Target: aletheia.DbcCommentTargetMessage{ID: 256, Extended: false}, Text: "msg scope"},
			{Target: aletheia.DbcCommentTargetSignal{ID: 256, Extended: false, Signal: "RPM"}, Text: "sig scope"},
			{Target: aletheia.DbcCommentTargetEnvVar{EnvVar: "AmbientTemp"}, Text: "env scope"},
		},
		Attributes: []aletheia.DbcAttribute{
			// 5 definitions, one per attr type kind. Float uses Rational
			// {-1,2} / {22,7} to prove ℚ precision survives the wire.
			aletheia.DbcAttrDef{
				Name: "IntAttr", Scope: aletheia.DbcAttrScopeNetwork,
				AttrType: aletheia.DbcAttrTypeInt{Min: 0, Max: 100},
			},
			aletheia.DbcAttrDef{
				Name: "FloatAttr", Scope: aletheia.DbcAttrScopeSignal,
				AttrType: aletheia.DbcAttrTypeFloat{
					Min: aletheia.Rational{Numerator: -1, Denominator: 2},
					Max: aletheia.Rational{Numerator: 22, Denominator: 7},
				},
			},
			aletheia.DbcAttrDef{
				Name: "StrAttr", Scope: aletheia.DbcAttrScopeMessage,
				AttrType: aletheia.DbcAttrTypeString{},
			},
			aletheia.DbcAttrDef{
				Name: "EnumAttr", Scope: aletheia.DbcAttrScopeNode,
				AttrType: aletheia.DbcAttrTypeEnum{Values: []string{"low", "high"}},
			},
			aletheia.DbcAttrDef{
				Name: "HexAttr", Scope: aletheia.DbcAttrScopeEnvVar,
				AttrType: aletheia.DbcAttrTypeHex{Min: 0, Max: 255},
			},
			// 1 default (int).
			aletheia.DbcAttrDefault{
				Name: "IntAttr", Value: aletheia.DbcAttrValueInt{Value: 42},
			},
			// 5 assignments — one per value kind AND one per less-covered
			// target kind (Network / Node / Signal / NodeMsg / NodeSig).
			aletheia.DbcAttrAssign{
				Name:   "IntAttr",
				Target: aletheia.DbcAttrTargetNetwork{},
				Value:  aletheia.DbcAttrValueInt{Value: 7},
			},
			aletheia.DbcAttrAssign{
				Name:   "FloatAttr",
				Target: aletheia.DbcAttrTargetNode{Node: "ECU"},
				Value: aletheia.DbcAttrValueFloat{
					Value: aletheia.Rational{Numerator: 1, Denominator: 3},
				},
			},
			aletheia.DbcAttrAssign{
				Name:   "StrAttr",
				Target: aletheia.DbcAttrTargetSignal{ID: 256, Extended: false, Signal: "RPM"},
				Value:  aletheia.DbcAttrValueString{Value: "hello"},
			},
			aletheia.DbcAttrAssign{
				Name:   "EnumAttr",
				Target: aletheia.DbcAttrTargetNodeMsg{Node: "ECU", ID: 256, Extended: false},
				Value:  aletheia.DbcAttrValueEnum{Value: 1},
			},
			aletheia.DbcAttrAssign{
				Name:   "HexAttr",
				Target: aletheia.DbcAttrTargetNodeSig{Node: "ECU", ID: 256, Extended: false, Signal: "RPM"},
				Value:  aletheia.DbcAttrValueHex{Value: 255},
			},
		},
	}
}

func TestSerializeDBC_Tier2RoundtripThroughMock(t *testing.T) {
	// Build a DBC carrying every Tier 2 variant, serialize through a
	// sendClient, re-wrap the captured envelope as a formatDBC response,
	// and parse it back through a parseClient. Every variant must
	// survive the round-trip unchanged.
	fixture := buildTier2Fixture(t)

	sendMock := aletheia.NewMockBackend(aletheia.Respond(`{"status":"success"}`))
	sendClient, err := aletheia.NewClient(sendMock)
	if err != nil {
		t.Fatal(err)
	}
	defer sendClient.Close()
	if err := sendClient.ParseDBC(fixture); err != nil {
		t.Fatalf("ParseDBC: %v", err)
	}

	envBytes := sendMock.Inputs()[0]
	var env map[string]any
	if err := json.Unmarshal([]byte(envBytes), &env); err != nil {
		t.Fatalf("envelope unmarshal: %v\n%s", err, envBytes)
	}
	respEnv := map[string]any{"status": "success", "dbc": env["dbc"]}
	respBytes, err := json.Marshal(respEnv)
	if err != nil {
		t.Fatalf("response marshal: %v", err)
	}

	parseMock := aletheia.NewMockBackend(aletheia.Respond(string(respBytes)))
	parseClient, err := aletheia.NewClient(parseMock)
	if err != nil {
		t.Fatal(err)
	}
	defer parseClient.Close()

	decoded, err := parseClient.FormatDBC()
	if err != nil {
		t.Fatalf("FormatDBC: %v", err)
	}

	// --- Nodes ---
	if got, want := len(decoded.Nodes), 2; got != want {
		t.Fatalf("Nodes: got %d, want %d", got, want)
	}
	if decoded.Nodes[0].Name != "ECU" || decoded.Nodes[1].Name != "Gateway" {
		t.Errorf("Nodes: got %v", decoded.Nodes)
	}

	// --- Comments: 5 variants ---
	if got, want := len(decoded.Comments), 5; got != want {
		t.Fatalf("Comments: got %d, want %d", got, want)
	}
	if _, ok := decoded.Comments[0].Target.(aletheia.DbcCommentTargetNetwork); !ok {
		t.Errorf("Comments[0]: want Network target, got %T", decoded.Comments[0].Target)
	}
	if node, ok := decoded.Comments[1].Target.(aletheia.DbcCommentTargetNode); !ok || node.Node != "ECU" {
		t.Errorf("Comments[1]: want Node{ECU}, got %v", decoded.Comments[1].Target)
	}
	if m, ok := decoded.Comments[2].Target.(aletheia.DbcCommentTargetMessage); !ok || m.ID != 256 || m.Extended {
		t.Errorf("Comments[2]: want Message{256,false}, got %v", decoded.Comments[2].Target)
	}
	if s, ok := decoded.Comments[3].Target.(aletheia.DbcCommentTargetSignal); !ok || s.Signal != "RPM" {
		t.Errorf("Comments[3]: want Signal{_,_,RPM}, got %v", decoded.Comments[3].Target)
	}
	if ev, ok := decoded.Comments[4].Target.(aletheia.DbcCommentTargetEnvVar); !ok || ev.EnvVar != "AmbientTemp" {
		t.Errorf("Comments[4]: want EnvVar{AmbientTemp}, got %v", decoded.Comments[4].Target)
	}
	if decoded.Comments[0].Text != "network scope" {
		t.Errorf("Comments[0].Text: got %q", decoded.Comments[0].Text)
	}

	// --- Attributes: 5 defs + 1 default + 5 assignments ---
	if got, want := len(decoded.Attributes), 11; got != want {
		t.Fatalf("Attributes: got %d, want %d", got, want)
	}

	// Attrs 0..4: definitions, one per type kind.
	intDef, ok := decoded.Attributes[0].(aletheia.DbcAttrDef)
	if !ok {
		t.Fatalf("Attributes[0]: want AttrDef, got %T", decoded.Attributes[0])
	}
	if intDef.Name != "IntAttr" || intDef.Scope != aletheia.DbcAttrScopeNetwork {
		t.Errorf("IntAttr def: got (%s, scope=%d)", intDef.Name, intDef.Scope)
	}
	if it, ok := intDef.AttrType.(aletheia.DbcAttrTypeInt); !ok || it.Min != 0 || it.Max != 100 {
		t.Errorf("IntAttr type: got %v", intDef.AttrType)
	}

	floatDef, _ := decoded.Attributes[1].(aletheia.DbcAttrDef)
	ft, ok := floatDef.AttrType.(aletheia.DbcAttrTypeFloat)
	if !ok {
		t.Fatalf("FloatAttr type: want AttrTypeFloat, got %T", floatDef.AttrType)
	}
	if ft.Min.Numerator != -1 || ft.Min.Denominator != 2 {
		t.Errorf("FloatAttr min: got %d/%d, want -1/2", ft.Min.Numerator, ft.Min.Denominator)
	}
	if ft.Max.Numerator != 22 || ft.Max.Denominator != 7 {
		t.Errorf("FloatAttr max: got %d/%d, want 22/7", ft.Max.Numerator, ft.Max.Denominator)
	}

	strDef, _ := decoded.Attributes[2].(aletheia.DbcAttrDef)
	if _, ok := strDef.AttrType.(aletheia.DbcAttrTypeString); !ok {
		t.Errorf("StrAttr type: want AttrTypeString, got %T", strDef.AttrType)
	}

	enumDef, _ := decoded.Attributes[3].(aletheia.DbcAttrDef)
	et, ok := enumDef.AttrType.(aletheia.DbcAttrTypeEnum)
	if !ok || len(et.Values) != 2 || et.Values[0] != "low" || et.Values[1] != "high" {
		t.Errorf("EnumAttr type: got %v", enumDef.AttrType)
	}

	hexDef, _ := decoded.Attributes[4].(aletheia.DbcAttrDef)
	if ht, ok := hexDef.AttrType.(aletheia.DbcAttrTypeHex); !ok || ht.Min != 0 || ht.Max != 255 {
		t.Errorf("HexAttr type: got %v", hexDef.AttrType)
	}

	// Attr 5: default (int).
	def, ok := decoded.Attributes[5].(aletheia.DbcAttrDefault)
	if !ok {
		t.Fatalf("Attributes[5]: want AttrDefault, got %T", decoded.Attributes[5])
	}
	if iv, ok := def.Value.(aletheia.DbcAttrValueInt); !ok || iv.Value != 42 {
		t.Errorf("IntAttr default: got %v", def.Value)
	}

	// Attrs 6..10: assignments, one per value kind + target kind mix.
	assignNet, ok := decoded.Attributes[6].(aletheia.DbcAttrAssign)
	if !ok {
		t.Fatalf("Attributes[6]: want AttrAssign, got %T", decoded.Attributes[6])
	}
	if _, ok := assignNet.Target.(aletheia.DbcAttrTargetNetwork); !ok {
		t.Errorf("assignNet target: want Network, got %T", assignNet.Target)
	}

	assignNode, _ := decoded.Attributes[7].(aletheia.DbcAttrAssign)
	if fv, ok := assignNode.Value.(aletheia.DbcAttrValueFloat); !ok ||
		fv.Value.Numerator != 1 || fv.Value.Denominator != 3 {
		t.Errorf("FloatAttr value: got %v", assignNode.Value)
	}
	if tgt, ok := assignNode.Target.(aletheia.DbcAttrTargetNode); !ok || tgt.Node != "ECU" {
		t.Errorf("assignNode target: got %v", assignNode.Target)
	}

	assignSig, _ := decoded.Attributes[8].(aletheia.DbcAttrAssign)
	if sv, ok := assignSig.Value.(aletheia.DbcAttrValueString); !ok || sv.Value != "hello" {
		t.Errorf("StrAttr value: got %v", assignSig.Value)
	}
	if sTgt, ok := assignSig.Target.(aletheia.DbcAttrTargetSignal); !ok || sTgt.Signal != "RPM" {
		t.Errorf("assignSig target: got %v", assignSig.Target)
	}

	assignNM, _ := decoded.Attributes[9].(aletheia.DbcAttrAssign)
	if ev, ok := assignNM.Value.(aletheia.DbcAttrValueEnum); !ok || ev.Value != 1 {
		t.Errorf("EnumAttr value: got %v", assignNM.Value)
	}
	if nm, ok := assignNM.Target.(aletheia.DbcAttrTargetNodeMsg); !ok ||
		nm.Node != "ECU" || nm.ID != 256 {
		t.Errorf("assignNM target: got %v", assignNM.Target)
	}

	assignNS, _ := decoded.Attributes[10].(aletheia.DbcAttrAssign)
	if hv, ok := assignNS.Value.(aletheia.DbcAttrValueHex); !ok || hv.Value != 255 {
		t.Errorf("HexAttr value: got %v", assignNS.Value)
	}
	if ns, ok := assignNS.Target.(aletheia.DbcAttrTargetNodeSig); !ok ||
		ns.Node != "ECU" || ns.Signal != "RPM" {
		t.Errorf("assignNS target: got %v", assignNS.Target)
	}
}

func TestFormatDBC_AcceptsMissingTier2Keys(t *testing.T) {
	mock := aletheia.NewMockBackend(aletheia.Respond(`{
		"status":"success",
		"dbc":{
			"version":"0.1",
			"messages":[]
		}
	}`))
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	dbc, err := c.FormatDBC()
	if err != nil {
		t.Fatalf("FormatDBC: %v", err)
	}
	if dbc.Nodes != nil {
		t.Errorf("Nodes: expected nil (absent key), got %v", dbc.Nodes)
	}
	if dbc.Comments != nil {
		t.Errorf("Comments: expected nil (absent key), got %v", dbc.Comments)
	}
	if dbc.Attributes != nil {
		t.Errorf("Attributes: expected nil (absent key), got %v", dbc.Attributes)
	}
}

func TestFormatDBC_RejectsUnknownCommentTargetKind(t *testing.T) {
	mock := aletheia.NewMockBackend(aletheia.Respond(`{
		"status":"success",
		"dbc":{
			"version":"0.1",
			"messages":[],
			"comments":[
				{"target":{"kind":"bogus"},"text":"bad"}
			]
		}
	}`))
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	_, err = c.FormatDBC()
	if err == nil {
		t.Fatal("expected error for unknown comment target kind, got nil")
	}
	if !strings.Contains(err.Error(), "comment target kind") {
		t.Errorf("error should mention comment target kind, got: %v", err)
	}
}

func TestDbcSignalReceivers_RoundtripThroughMock(t *testing.T) {
	// Build a single-signal DBC with explicit Receivers, serialize it
	// through parseDBC, rebuild the response envelope, parse it back
	// through formatDBC, and confirm Receivers survived unchanged.
	id, err := aletheia.NewStandardID(256)
	if err != nil {
		t.Fatal(err)
	}
	dlc, err := aletheia.BytesToDLC(8)
	if err != nil {
		t.Fatal(err)
	}
	sig := aletheia.DbcSignal{
		Name:      "Speed",
		StartBit:  0,
		BitLength: 16,
		ByteOrder: aletheia.LittleEndian,
		Factor:    aletheia.Rational{Numerator: 1, Denominator: 1},
		Offset:    aletheia.Rational{Numerator: 0, Denominator: 1},
		Minimum:   aletheia.Rational{Numerator: 0, Denominator: 1},
		Maximum:   aletheia.Rational{Numerator: 255, Denominator: 1},
		Unit:      "km/h",
		Presence:  aletheia.AlwaysPresent{},
		Receivers: []string{"ECU_A", "ECU_B"},
	}
	msg := aletheia.NewDbcMessage(id, "VehicleSpeed", dlc, "ECU", nil, []aletheia.DbcSignal{sig})
	fixture := aletheia.DbcDefinition{
		Version:  "1.0",
		Messages: []aletheia.DbcMessage{msg},
	}

	sendMock := aletheia.NewMockBackend(aletheia.Respond(`{"status":"success"}`))
	sendClient, err := aletheia.NewClient(sendMock)
	if err != nil {
		t.Fatal(err)
	}
	defer sendClient.Close()
	if err := sendClient.ParseDBC(fixture); err != nil {
		t.Fatalf("ParseDBC: %v", err)
	}

	envBytes := sendMock.Inputs()[0]
	var env map[string]any
	if err := json.Unmarshal([]byte(envBytes), &env); err != nil {
		t.Fatalf("envelope unmarshal: %v\n%s", err, envBytes)
	}
	// Confirm wire shape: receivers is present on the outgoing signal.
	dbcObj, ok := env["dbc"].(map[string]any)
	if !ok {
		t.Fatalf("dbc object missing from envelope")
	}
	msgs, _ := dbcObj["messages"].([]any)
	if len(msgs) != 1 {
		t.Fatalf("messages: want 1, got %d", len(msgs))
	}
	sigs, _ := msgs[0].(map[string]any)["signals"].([]any)
	if len(sigs) != 1 {
		t.Fatalf("signals: want 1, got %d", len(sigs))
	}
	wireRecv, ok := sigs[0].(map[string]any)["receivers"].([]any)
	if !ok {
		t.Fatalf("receivers: missing or not an array")
	}
	if len(wireRecv) != 2 || wireRecv[0] != "ECU_A" || wireRecv[1] != "ECU_B" {
		t.Errorf("wire receivers: got %v, want [ECU_A ECU_B]", wireRecv)
	}

	respEnv := map[string]any{"status": "success", "dbc": dbcObj}
	respBytes, err := json.Marshal(respEnv)
	if err != nil {
		t.Fatalf("response marshal: %v", err)
	}
	parseMock := aletheia.NewMockBackend(aletheia.Respond(string(respBytes)))
	parseClient, err := aletheia.NewClient(parseMock)
	if err != nil {
		t.Fatal(err)
	}
	defer parseClient.Close()

	decoded, err := parseClient.FormatDBC()
	if err != nil {
		t.Fatalf("FormatDBC: %v", err)
	}
	if len(decoded.Messages) != 1 || len(decoded.Messages[0].Signals) != 1 {
		t.Fatalf("decoded shape: want 1 msg / 1 sig, got %d / %d",
			len(decoded.Messages), len(decoded.Messages[0].Signals))
	}
	got := decoded.Messages[0].Signals[0].Receivers
	if len(got) != 2 || got[0] != "ECU_A" || got[1] != "ECU_B" {
		t.Errorf("decoded receivers: got %v, want [ECU_A ECU_B]", got)
	}
}

func TestDbcSignalReceivers_EmptyWhenAbsent(t *testing.T) {
	// A parseDBC response that omits "receivers" entirely must parse
	// cleanly with Receivers == nil (not an error).
	mock := aletheia.NewMockBackend(aletheia.Respond(`{
		"status":"success",
		"dbc":{
			"version":"1.0",
			"messages":[{
				"id":256,"name":"M","dlc":8,"sender":"ECU","extended":false,
				"signals":[{
					"name":"S","startBit":0,"length":8,"byteOrder":"little_endian",
					"signed":false,
					"factor":{"numerator":1,"denominator":1},
					"offset":{"numerator":0,"denominator":1},
					"minimum":{"numerator":0,"denominator":1},
					"maximum":{"numerator":255,"denominator":1},
					"unit":""
				}]
			}]
		}
	}`))
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()
	dbc, err := c.FormatDBC()
	if err != nil {
		t.Fatalf("FormatDBC: %v", err)
	}
	if len(dbc.Messages) != 1 || len(dbc.Messages[0].Signals) != 1 {
		t.Fatalf("unexpected shape: %+v", dbc)
	}
	if got := dbc.Messages[0].Signals[0].Receivers; got != nil {
		t.Errorf("absent receivers: want nil, got %v", got)
	}
}

func TestDbcMessageSenders_RoundtripThroughMock(t *testing.T) {
	// BO_TX_BU_ additional senders: primary in Sender, extras in Senders.
	// Mirrors TestDbcSignalReceivers_RoundtripThroughMock for the new
	// message-level wire key.
	id, err := aletheia.NewStandardID(256)
	if err != nil {
		t.Fatal(err)
	}
	dlc, err := aletheia.BytesToDLC(8)
	if err != nil {
		t.Fatal(err)
	}
	msg := aletheia.NewDbcMessage(id, "VehicleSpeed", dlc, "ECU_A",
		[]string{"ECU_B", "ECU_C"}, nil)
	fixture := aletheia.DbcDefinition{
		Version:  "1.0",
		Messages: []aletheia.DbcMessage{msg},
	}

	sendMock := aletheia.NewMockBackend(aletheia.Respond(`{"status":"success"}`))
	sendClient, err := aletheia.NewClient(sendMock)
	if err != nil {
		t.Fatal(err)
	}
	defer sendClient.Close()
	if err := sendClient.ParseDBC(fixture); err != nil {
		t.Fatalf("ParseDBC: %v", err)
	}

	envBytes := sendMock.Inputs()[0]
	var env map[string]any
	if err := json.Unmarshal([]byte(envBytes), &env); err != nil {
		t.Fatalf("envelope unmarshal: %v\n%s", err, envBytes)
	}
	dbcObj, ok := env["dbc"].(map[string]any)
	if !ok {
		t.Fatalf("dbc object missing from envelope")
	}
	msgs, _ := dbcObj["messages"].([]any)
	if len(msgs) != 1 {
		t.Fatalf("messages: want 1, got %d", len(msgs))
	}
	wireSenders, ok := msgs[0].(map[string]any)["senders"].([]any)
	if !ok {
		t.Fatalf("senders: missing or not an array")
	}
	if len(wireSenders) != 2 || wireSenders[0] != "ECU_B" || wireSenders[1] != "ECU_C" {
		t.Errorf("wire senders: got %v, want [ECU_B ECU_C]", wireSenders)
	}

	respEnv := map[string]any{"status": "success", "dbc": dbcObj}
	respBytes, err := json.Marshal(respEnv)
	if err != nil {
		t.Fatalf("response marshal: %v", err)
	}
	parseMock := aletheia.NewMockBackend(aletheia.Respond(string(respBytes)))
	parseClient, err := aletheia.NewClient(parseMock)
	if err != nil {
		t.Fatal(err)
	}
	defer parseClient.Close()

	decoded, err := parseClient.FormatDBC()
	if err != nil {
		t.Fatalf("FormatDBC: %v", err)
	}
	if len(decoded.Messages) != 1 {
		t.Fatalf("decoded shape: want 1 msg, got %d", len(decoded.Messages))
	}
	got := decoded.Messages[0].Senders
	if len(got) != 2 || got[0] != "ECU_B" || got[1] != "ECU_C" {
		t.Errorf("decoded senders: got %v, want [ECU_B ECU_C]", got)
	}
}

func TestDbcMessageSenders_EmptyWhenAbsent(t *testing.T) {
	// Pre-B.1.x DBC responses may omit "senders"; parser defaults to nil.
	mock := aletheia.NewMockBackend(aletheia.Respond(`{
		"status":"success",
		"dbc":{
			"version":"1.0",
			"messages":[{
				"id":256,"name":"M","dlc":8,"sender":"ECU","extended":false,
				"signals":[]
			}]
		}
	}`))
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()
	dbc, err := c.FormatDBC()
	if err != nil {
		t.Fatalf("FormatDBC: %v", err)
	}
	if len(dbc.Messages) != 1 {
		t.Fatalf("unexpected shape: %+v", dbc)
	}
	if got := dbc.Messages[0].Senders; got != nil {
		t.Errorf("absent senders: want nil, got %v", got)
	}
}

func TestSerializeDBC_EmitsEmptyTier2ArraysWhenMetadataAbsent(t *testing.T) {
	mock := aletheia.NewMockBackend(aletheia.Respond(`{"status":"success"}`))
	c, err := aletheia.NewClient(mock)
	if err != nil {
		t.Fatal(err)
	}
	defer c.Close()

	id, _ := aletheia.NewStandardID(256)
	dlc, _ := aletheia.BytesToDLC(8)
	msg := aletheia.NewDbcMessage(id, "MinimalMsg", dlc, "ECU", nil, nil)
	dbc := aletheia.DbcDefinition{
		Version:  "1.0",
		Messages: []aletheia.DbcMessage{msg},
		// All Tier 1 & Tier 2 slices left nil — every key must still
		// land on the wire as an empty array.
	}
	if err := c.ParseDBC(dbc); err != nil {
		t.Fatalf("ParseDBC: %v", err)
	}

	inputs := mock.Inputs()
	dbcObj := extractDbcObject(t, inputs[0])

	for _, key := range []string{"nodes", "comments", "attributes"} {
		arr, ok := dbcObj[key].([]any)
		if !ok {
			t.Errorf("%s: missing or not an array, got %T", key, dbcObj[key])
			continue
		}
		if len(arr) != 0 {
			t.Errorf("%s: expected empty array, got %d items", key, len(arr))
		}
	}
}
