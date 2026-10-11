// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"fmt"
	"math"
)

// parseDBCResponse decodes a formatDBC response into a DBCDefinition.
func parseDBCResponse(raw string) (*DBCDefinition, error) {
	m, err := decodeResponse(raw, "success")
	if err != nil {
		return nil, err
	}

	dbcRaw := getObject(m, "dbc")
	if dbcRaw == nil {
		return nil, protocolError("missing 'dbc' field in response")
	}
	return parseDBCDefinition(dbcRaw)
}

// parseDBCTextResponse decodes a formatDBCText response into the .dbc text image
// plus its wfTextIssues diagnostics.  A round-trip refusal
// (handler_text_roundtrip_failed) is lifted by checkErrorStatus into a typed
// [TextRoundTripFailedError], and a size-bound refusal (input_bound_exceeded)
// into a typed [InputBoundExceededError]; those and other errors (Agda-side
// JSON parse failure on the input, unexpected status) short-circuit to the
// (*DBCText, error) tuple's error half.
func parseDBCTextResponse(raw string) (*DBCText, error) {
	m, err := decodeResponse(raw, "success")
	if err != nil {
		return nil, err
	}
	text, ok := m["text"].(string)
	if !ok {
		return nil, protocolError("missing or non-string 'text' field in formatDBCText response")
	}
	// Absent issues → empty; a present-but-non-array issues field is a protocol
	// error, not silently dropped to empty (parseIssueArray/getArray treat a
	// wrong-type field as missing). Parity with the Python/Rust decoders.
	if raw, present := m["issues"]; present {
		if _, isArray := raw.([]any); !isArray {
			return nil, protocolError("'issues' must be an array in formatDBCText response")
		}
	}
	issues, err := parseIssueArray(m, "issues")
	if err != nil {
		return nil, err
	}
	return &DBCText{Text: text, Issues: issues}, nil
}

// parseParsedDBCResponse decodes a parseDBC / parseDBCText success response
// into typed (*ParsedDBC) form: the parsed body plus any non-error issues
// (warnings).  Errors short-circuit to the (*ParsedDBC, error) tuple's
// error half.
func parseParsedDBCResponse(raw string) (*ParsedDBC, error) {
	m, err := decodeResponse(raw, "success")
	if err != nil {
		return nil, err
	}

	dbcRaw := getObject(m, "dbc")
	if dbcRaw == nil {
		return nil, protocolError("missing 'dbc' field in parseDBC response")
	}
	dbc, err := parseDBCDefinition(dbcRaw)
	if err != nil {
		return nil, err
	}

	warnings, err := parseIssueArray(m, "warnings")
	if err != nil {
		return nil, err
	}
	return &ParsedDBC{DBC: *dbc, Warnings: warnings}, nil
}

// parseDBCDefinition decodes the definition a response carries. Its metadata
// arrays are optional: an absent or null key reads as none.
func parseDBCDefinition(j map[string]any) (*DBCDefinition, error) {
	var messages []DBCMessage
	for _, item := range getArray(j, "messages") {
		mRaw, ok := item.(map[string]any)
		if !ok {
			return nil, protocolError("expected object in messages array")
		}
		msg, err := parseDBCMessage(mRaw)
		if err != nil {
			return nil, err
		}
		messages = append(messages, *msg)
	}

	signalGroups, err := parseSignalGroups(j)
	if err != nil {
		return nil, err
	}
	envVars, err := parseEnvironmentVars(j)
	if err != nil {
		return nil, err
	}
	valueTables, err := parseValueTables(j)
	if err != nil {
		return nil, err
	}
	nodes, err := parseNodes(j)
	if err != nil {
		return nil, err
	}
	comments, err := parseComments(j)
	if err != nil {
		return nil, err
	}
	attributes, err := parseAttributes(j)
	if err != nil {
		return nil, err
	}
	unresolvedValueDescs, err := parseUnresolvedValueDescs(j)
	if err != nil {
		return nil, err
	}

	def := &DBCDefinition{
		Version:                     getString(j, "version"),
		Messages:                    messages,
		SignalGroups:                signalGroups,
		EnvironmentVars:             envVars,
		ValueTables:                 valueTables,
		Nodes:                       nodes,
		Comments:                    comments,
		Attributes:                  attributes,
		UnresolvedValueDescriptions: unresolvedValueDescs,
	}
	def.buildIndexes()
	return def, nil
}

// parseObjects decodes an array of objects under a key: nothing for an absent
// or empty field, a refusal at the first entry that is not an object, and the
// entry decoder's own error otherwise. Every list the DBC carries is read
// through it, each passing what one entry means.
func parseObjects[T any](
	j map[string]any,
	fieldName string,
	decode func(map[string]any) (T, error),
) ([]T, error) {
	raw := getArray(j, fieldName)
	if len(raw) == 0 {
		return nil, nil
	}
	out := make([]T, 0, len(raw))
	for _, item := range raw {
		m, ok := item.(map[string]any)
		if !ok {
			return nil, protocolError(fmt.Sprintf("expected object in %s array", fieldName))
		}
		v, err := decode(m)
		if err != nil {
			return nil, err
		}
		out = append(out, v)
	}
	return out, nil
}

// parseUnresolvedValueDescs decodes the value descriptions the text parser
// could not attach to a signal. The field is usually absent.
func parseUnresolvedValueDescs(j map[string]any) ([]DBCRawValueDesc, error) {
	return parseObjects(j, "unresolvedValueDescs", func(rvdRaw map[string]any) (DBCRawValueDesc, error) {
		canID, err := parseCanIDValue(rvdRaw)
		if err != nil {
			return DBCRawValueDesc{}, wrapProtocolError("invalid unresolvedValueDesc id", err)
		}
		entries, err := parseObjects(rvdRaw, "entries", func(eRaw map[string]any) (DBCValueEntry, error) {
			v, err := parseNumberAsInt64(eRaw["value"])
			if err != nil {
				return DBCValueEntry{}, wrapProtocolError("invalid unresolvedValueDescs entry value", err)
			}
			return DBCValueEntry{
				Value:       v,
				Description: getString(eRaw, "description"),
			}, nil
		})
		if err != nil {
			return DBCRawValueDesc{}, err
		}
		return DBCRawValueDesc{
			ID:         canID,
			SignalName: SignalName(getString(rvdRaw, "signalName")),
			Entries:    entries,
		}, nil
	})
}

// parseSignalGroups decodes the optional "signalGroups" array from a
// formatDBC "dbc" sub-object.
func parseSignalGroups(j map[string]any) ([]DBCSignalGroup, error) {
	return parseObjects(j, "signalGroups", func(gRaw map[string]any) (DBCSignalGroup, error) {
		sigsRaw := getArray(gRaw, "signals")
		sigs := make([]SignalName, 0, len(sigsRaw))
		for _, sn := range sigsRaw {
			s, ok := sn.(string)
			if !ok {
				return DBCSignalGroup{}, protocolError("signalGroups.signals entry is not a string")
			}
			sigs = append(sigs, SignalName(s))
		}
		return DBCSignalGroup{Name: getString(gRaw, "name"), Signals: sigs}, nil
	})
}

// parseEnvironmentVars decodes the environment variables. The type tag is one
// of the three the format has, and any other number is refused.
func parseEnvironmentVars(j map[string]any) ([]DBCEnvironmentVar, error) {
	return parseObjects(j, "environmentVars", func(evRaw map[string]any) (DBCEnvironmentVar, error) {
		tagVal, err := parseNumberAsInt64(evRaw["varType"])
		if err != nil {
			return DBCEnvironmentVar{}, wrapProtocolError("invalid varType", err)
		}
		if tagVal < 0 || tagVal > 2 {
			return DBCEnvironmentVar{}, protocolError(fmt.Sprintf("unknown varType tag: %d", tagVal))
		}
		initial, err := parseRational(evRaw["initial"])
		if err != nil {
			return DBCEnvironmentVar{}, wrapProtocolError("invalid environmentVar initial", err)
		}
		minimum, err := parseRational(evRaw["minimum"])
		if err != nil {
			return DBCEnvironmentVar{}, wrapProtocolError("invalid environmentVar minimum", err)
		}
		maximum, err := parseRational(evRaw["maximum"])
		if err != nil {
			return DBCEnvironmentVar{}, wrapProtocolError("invalid environmentVar maximum", err)
		}
		return DBCEnvironmentVar{
			Name:    getString(evRaw, "name"),
			VarType: DBCVarType(tagVal),
			Initial: initial,
			Minimum: minimum,
			Maximum: maximum,
		}, nil
	})
}

// parseValueTables decodes the value tables, each entry's value read exactly.
func parseValueTables(j map[string]any) ([]DBCValueTable, error) {
	return parseObjects(j, "valueTables", func(vtRaw map[string]any) (DBCValueTable, error) {
		entries, err := parseObjects(vtRaw, "entries", func(eRaw map[string]any) (DBCValueEntry, error) {
			v, err := parseNumberAsInt64(eRaw["value"])
			if err != nil {
				return DBCValueEntry{}, wrapProtocolError("invalid valueTable entry value", err)
			}
			return DBCValueEntry{
				Value:       v,
				Description: getString(eRaw, "description"),
			}, nil
		})
		if err != nil {
			return DBCValueTable{}, err
		}
		return DBCValueTable{
			Name:    getString(vtRaw, "name"),
			Entries: entries,
		}, nil
	})
}

// --- Tier 2 parsers ---

// parseNodes decodes the optional "nodes" array.
func parseNodes(j map[string]any) ([]DBCNode, error) {
	return parseObjects(j, "nodes", func(nRaw map[string]any) (DBCNode, error) {
		return DBCNode{Name: NodeName(getString(nRaw, "name"))}, nil
	})
}

// canIDOfWidth is the identifier of the width extended names. A standard value
// past sixteen bits is refused before the constructor sees it, since the
// conversion to its argument would keep only the low bits.
func canIDOfWidth(raw uint32, extended bool) (CANID, error) {
	if extended {
		id, err := NewExtendedID(raw)
		if err != nil {
			return nil, wrapProtocolError("invalid extended id", err)
		}
		return id, nil
	}
	narrowed, ok := narrow[uint16](int64(raw))
	if !ok {
		return nil, protocolError(fmt.Sprintf("standard id out of range: %d", raw))
	}
	id, err := NewStandardID(narrowed)
	if err != nil {
		return nil, wrapProtocolError("invalid standard id", err)
	}
	return id, nil
}

// parseCanIDValue reads the identifier every message-scoped or signal-scoped
// target carries, an absent extended flag meaning a standard one. The width
// the flag names is checked, so a target naming a message no frame could carry
// is refused at the parse rather than kept.
func parseCanIDValue(m map[string]any) (CANID, error) {
	idVal, err := parseNumberAsInt64(m["id"])
	if err != nil {
		return nil, wrapProtocolError("invalid id", err)
	}
	raw, ok := narrow[uint32](idVal)
	if !ok {
		return nil, protocolError(fmt.Sprintf("id out of uint32 range: %d", idVal))
	}
	return canIDOfWidth(raw, getBool(m, "extended"))
}

// parseCommentTarget decodes what a comment is attached to, refusing a kind
// the format does not have, as the kernel's own parser does.
func parseCommentTarget(m map[string]any) (DBCCommentTarget, error) {
	kind := getString(m, "kind")
	switch kind {
	case "network":
		return DBCCommentTargetNetwork{}, nil
	case "node":
		return DBCCommentTargetNode{Node: NodeName(getString(m, "node"))}, nil
	case "message":
		id, err := parseCanIDValue(m)
		if err != nil {
			return nil, err
		}
		return DBCCommentTargetMessage{ID: id}, nil
	case "signal":
		id, err := parseCanIDValue(m)
		if err != nil {
			return nil, err
		}
		return DBCCommentTargetSignal{ID: id, Signal: SignalName(getString(m, "signal"))}, nil
	case "envVar":
		return DBCCommentTargetEnvVar{EnvVar: getString(m, "envVar")}, nil
	default:
		return nil, protocolError(fmt.Sprintf("unknown comment target kind: %q", kind))
	}
}

// parseComments decodes the optional "comments" array.
func parseComments(j map[string]any) ([]DBCComment, error) {
	return parseObjects(j, "comments", func(cRaw map[string]any) (DBCComment, error) {
		targetRaw, ok := cRaw["target"].(map[string]any)
		if !ok {
			return DBCComment{}, protocolError("comment entry missing target object")
		}
		target, err := parseCommentTarget(targetRaw)
		if err != nil {
			return DBCComment{}, err
		}
		return DBCComment{Target: target, Text: getString(cRaw, "text")}, nil
	})
}

func parseAttrScope(s string) (DBCAttrScope, error) {
	switch s {
	case "network":
		return DBCAttrScopeNetwork, nil
	case "node":
		return DBCAttrScopeNode, nil
	case "message":
		return DBCAttrScopeMessage, nil
	case "signal":
		return DBCAttrScopeSignal, nil
	case "envVar":
		return DBCAttrScopeEnvVar, nil
	case "nodeMsg":
		return DBCAttrScopeNodeMsg, nil
	case "nodeSig":
		return DBCAttrScopeNodeSig, nil
	default:
		return 0, protocolError(fmt.Sprintf("unknown attr scope: %q", s))
	}
}

func parseAttrType(m map[string]any) (DBCAttrType, error) {
	kind := getString(m, "kind")
	switch kind {
	case "int":
		minV, err := parseNumberAsInt64(m["min"])
		if err != nil {
			return nil, wrapProtocolError("invalid int attr min", err)
		}
		maxV, err := parseNumberAsInt64(m["max"])
		if err != nil {
			return nil, wrapProtocolError("invalid int attr max", err)
		}
		return DBCAttrTypeInt{Min: minV, Max: maxV}, nil
	case "float":
		minV, err := parseRational(m["min"])
		if err != nil {
			return nil, wrapProtocolError("invalid float attr min", err)
		}
		maxV, err := parseRational(m["max"])
		if err != nil {
			return nil, wrapProtocolError("invalid float attr max", err)
		}
		return DBCAttrTypeFloat{Min: minV, Max: maxV}, nil
	case "string":
		return DBCAttrTypeString{}, nil
	case "enum":
		valuesRaw := getArray(m, "values")
		values := make([]string, 0, len(valuesRaw))
		for _, vr := range valuesRaw {
			s, ok := vr.(string)
			if !ok {
				return nil, protocolError("enum attr type values entry is not a string")
			}
			values = append(values, s)
		}
		return DBCAttrTypeEnum{Values: values}, nil
	case "hex":
		minV, err := parseNumberAsInt64(m["min"])
		if err != nil {
			return nil, wrapProtocolError("invalid hex attr min", err)
		}
		maxV, err := parseNumberAsInt64(m["max"])
		if err != nil {
			return nil, wrapProtocolError("invalid hex attr max", err)
		}
		return DBCAttrTypeHex{Min: minV, Max: maxV}, nil
	default:
		return nil, protocolError(fmt.Sprintf("unknown attr type kind: %q", kind))
	}
}

func parseAttrValue(m map[string]any) (DBCAttrValue, error) {
	kind := getString(m, "kind")
	switch kind {
	case "int":
		v, err := parseNumberAsInt64(m["value"])
		if err != nil {
			return nil, wrapProtocolError("invalid int attr value", err)
		}
		return DBCAttrValueInt{Value: v}, nil
	case "float":
		v, err := parseRational(m["value"])
		if err != nil {
			return nil, wrapProtocolError("invalid float attr value", err)
		}
		return DBCAttrValueFloat{Value: v}, nil
	case "string":
		return DBCAttrValueString{Value: getString(m, "value")}, nil
	case "enum":
		v, err := parseNumberAsInt64(m["value"])
		if err != nil {
			return nil, wrapProtocolError("invalid enum attr value", err)
		}
		return DBCAttrValueEnum{Value: v}, nil
	case "hex":
		v, err := parseNumberAsInt64(m["value"])
		if err != nil {
			return nil, wrapProtocolError("invalid hex attr value", err)
		}
		return DBCAttrValueHex{Value: v}, nil
	default:
		return nil, protocolError(fmt.Sprintf("unknown attr value kind: %q", kind))
	}
}

func parseAttrTarget(m map[string]any) (DBCAttrTarget, error) {
	kind := getString(m, "kind")
	switch kind {
	case "network":
		return DBCAttrTargetNetwork{}, nil
	case "node":
		return DBCAttrTargetNode{Node: NodeName(getString(m, "node"))}, nil
	case "message":
		id, err := parseCanIDValue(m)
		if err != nil {
			return nil, err
		}
		return DBCAttrTargetMessage{ID: id}, nil
	case "signal":
		id, err := parseCanIDValue(m)
		if err != nil {
			return nil, err
		}
		return DBCAttrTargetSignal{ID: id, Signal: SignalName(getString(m, "signal"))}, nil
	case "envVar":
		return DBCAttrTargetEnvVar{EnvVar: getString(m, "envVar")}, nil
	case "nodeMsg":
		id, err := parseCanIDValue(m)
		if err != nil {
			return nil, err
		}
		return DBCAttrTargetNodeMsg{Node: NodeName(getString(m, "node")), ID: id}, nil
	case "nodeSig":
		id, err := parseCanIDValue(m)
		if err != nil {
			return nil, err
		}
		return DBCAttrTargetNodeSig{
			Node:   NodeName(getString(m, "node")),
			ID:     id,
			Signal: SignalName(getString(m, "signal")),
		}, nil
	default:
		return nil, protocolError(fmt.Sprintf("unknown attr target kind: %q", kind))
	}
}

func parseAttribute(m map[string]any) (DBCAttribute, error) {
	kind := getString(m, "kind")
	switch kind {
	case "definition":
		scope, err := parseAttrScope(getString(m, "scope"))
		if err != nil {
			return nil, err
		}
		atRaw, ok := m["attrType"].(map[string]any)
		if !ok {
			return nil, protocolError("attribute definition missing attrType object")
		}
		at, err := parseAttrType(atRaw)
		if err != nil {
			return nil, err
		}
		return DBCAttrDef{Name: getString(m, "name"), Scope: scope, AttrType: at}, nil
	case "default":
		valRaw, ok := m["value"].(map[string]any)
		if !ok {
			return nil, protocolError("attribute default missing value object")
		}
		val, err := parseAttrValue(valRaw)
		if err != nil {
			return nil, err
		}
		return DBCAttrDefault{Name: getString(m, "name"), Value: val}, nil
	case "assignment":
		targetRaw, ok := m["target"].(map[string]any)
		if !ok {
			return nil, protocolError("attribute assignment missing target object")
		}
		target, err := parseAttrTarget(targetRaw)
		if err != nil {
			return nil, err
		}
		valRaw, ok := m["value"].(map[string]any)
		if !ok {
			return nil, protocolError("attribute assignment missing value object")
		}
		val, err := parseAttrValue(valRaw)
		if err != nil {
			return nil, err
		}
		return DBCAttrAssign{Name: getString(m, "name"), Target: target, Value: val}, nil
	default:
		return nil, protocolError(fmt.Sprintf("unknown attribute kind: %q", kind))
	}
}

// parseAttributes decodes the optional "attributes" array.
func parseAttributes(j map[string]any) ([]DBCAttribute, error) {
	return parseObjects(j, "attributes", parseAttribute)
}

// parseDBCMessage decodes a single message from a DBCDefinition JSON
// object, including its signals and multiplexing metadata.
func parseDBCMessage(j map[string]any) (*DBCMessage, error) {
	idVal, err := parseNumberAsInt64(j["id"])
	if err != nil {
		return nil, wrapProtocolError("invalid message id", err)
	}
	raw, ok := narrow[uint32](idVal)
	if !ok {
		return nil, protocolError(fmt.Sprintf("message id out of uint32 range: %d", idVal))
	}
	extended := false
	if v, ok := j["extended"]; ok {
		b, isBool := v.(bool)
		if !isBool {
			return nil, protocolError("message \"extended\" must be a boolean")
		}
		extended = b
	}
	id, err := canIDOfWidth(raw, extended)
	if err != nil {
		return nil, err
	}

	dlcVal, err := parseNumberAsInt64(j["dlc"])
	if err != nil {
		return nil, wrapProtocolError("invalid DLC", err)
	}
	dlc, err := BytesToDLC(int(dlcVal))
	if err != nil {
		return nil, err
	}

	var signals []DBCSignal
	for _, item := range getArray(j, "signals") {
		sRaw, ok := item.(map[string]any)
		if !ok {
			return nil, protocolError("expected object in signals array")
		}
		sig, err := parseDBCSignal(sRaw)
		if err != nil {
			return nil, err
		}
		signals = append(signals, sig)
	}

	msgName := getString(j, "name")
	if msgName == "" {
		return nil, protocolError("message missing required field: name")
	}

	var senders []NodeName
	if raw, ok := j["senders"].([]any); ok {
		senders = make([]NodeName, 0, len(raw))
		for _, s := range raw {
			ss, sOk := s.(string)
			if !sOk {
				return nil, protocolError("senders entry is not a string")
			}
			senders = append(senders, NodeName(ss))
		}
	}

	msg := &DBCMessage{
		ID:      id,
		Name:    MessageName(msgName),
		DLC:     dlc,
		Sender:  NodeName(getString(j, "sender")),
		Senders: senders,
		Signals: signals,
	}
	msg.buildSignalIndex()
	return msg, nil
}

// parseDBCSignal decodes one signal definition from a DBC JSON object.
func parseDBCSignal(j map[string]any) (DBCSignal, error) {
	var zero DBCSignal
	var bo ByteOrder
	switch name := getString(j, "byteOrder"); name {
	case LittleEndian.String():
		bo = LittleEndian
	case BigEndian.String():
		bo = BigEndian
	default:
		return zero, protocolError(fmt.Sprintf("unrecognized byte order: %q", name))
	}

	factor, err := parseRational(j["factor"])
	if err != nil {
		return zero, wrapProtocolError("invalid factor", err)
	}
	offset, err := parseRational(j["offset"])
	if err != nil {
		return zero, wrapProtocolError("invalid offset", err)
	}
	minimum, err := parseRational(j["minimum"])
	if err != nil {
		return zero, wrapProtocolError("invalid minimum", err)
	}
	maximum, err := parseRational(j["maximum"])
	if err != nil {
		return zero, wrapProtocolError("invalid maximum", err)
	}
	startBit, err := parseNumberAsInt64(j["startBit"])
	if err != nil {
		return zero, wrapProtocolError("invalid startBit", err)
	}
	if startBit < 0 || startBit > 511 {
		return zero, protocolError(fmt.Sprintf("startBit %d out of range (0-511)", startBit))
	}
	length, err := parseNumberAsInt64(j["length"])
	if err != nil {
		return zero, wrapProtocolError("invalid length", err)
	}
	if length < 1 || length > MaxBitLength {
		return zero, protocolError(fmt.Sprintf("bit length %d out of range (1-%d)", length, MaxBitLength))
	}

	presence, err := parseSignalPresence(j)
	if err != nil {
		return zero, err
	}

	name := getString(j, "name")
	if name == "" {
		return zero, protocolError("signal missing required field: name")
	}

	// A signal the kernel wrote says whether it is signed. Missing, it reads as
	// unsigned, which is the format's default, rather than failing the parse:
	// the caller cannot act on drift between the binding and the kernel.
	isSigned := false
	if b, ok := j["signed"].(bool); ok {
		isSigned = b
	}

	var receivers []NodeName
	if raw, ok := j["receivers"].([]any); ok {
		receivers = make([]NodeName, 0, len(raw))
		for _, r := range raw {
			rs, rOk := r.(string)
			if !rOk {
				return zero, protocolError("receivers entry is not a string")
			}
			receivers = append(receivers, NodeName(rs))
		}
	}

	var valueDescriptions []DBCValueEntry
	if raw, ok := j["valueDescriptions"].([]any); ok {
		valueDescriptions = make([]DBCValueEntry, 0, len(raw))
		for _, item := range raw {
			eMap, eOk := item.(map[string]any)
			if !eOk {
				return zero, protocolError("expected object in valueDescriptions array")
			}
			v, err := parseNumberAsInt64(eMap["value"])
			if err != nil {
				return zero, wrapProtocolError("invalid valueDescriptions entry value", err)
			}
			valueDescriptions = append(valueDescriptions, DBCValueEntry{
				Value:       v,
				Description: getString(eMap, "description"),
			})
		}
	}

	return DBCSignal{
		Name:              SignalName(name),
		StartBit:          BitPosition(startBit),
		BitLength:         BitLength(length),
		ByteOrder:         bo,
		IsSigned:          isSigned,
		Factor:            factor,
		Offset:            offset,
		Minimum:           minimum,
		Maximum:           maximum,
		Unit:              Unit(getString(j, "unit")),
		Presence:          presence,
		Receivers:         receivers,
		ValueDescriptions: valueDescriptions,
	}, nil
}

// parseSignalPresence reads the presence the kernel states for every signal,
// rather than inferring it from a multiplexor field being there, which is how
// the other bindings read it too. A multiplexed signal must name its
// multiplexor and carry at least one value.
func parseSignalPresence(j map[string]any) (SignalPresence, error) {
	switch presence := getString(j, "presence"); presence {
	case "always":
		return AlwaysPresent{}, nil
	case "multiplexed":
		muxName := getString(j, "multiplexor")
		if muxName == "" {
			return nil, protocolError("multiplexed signal requires a non-empty \"multiplexor\"")
		}
		// Anything but an array, absence included, asserts to a nil slice.
		rawVals, _ := j["multiplex_values"].([]any)
		if len(rawVals) == 0 {
			return nil, protocolError("multiplexed signal requires a non-empty \"multiplex_values\" array")
		}
		muxVals := make([]MultiplexValue, 0, len(rawVals))
		for i, rv := range rawVals {
			v, err := parseNumberAsInt64(rv)
			if err != nil {
				return nil, wrapProtocolError(fmt.Sprintf("invalid multiplex_values[%d]", i), err)
			}
			mv, ok := narrow[MultiplexValue](v)
			if !ok {
				return nil, protocolError(fmt.Sprintf("multiplex_values[%d] %d out of range (0-%d)", i, v, uint32(math.MaxUint32)))
			}
			muxVals = append(muxVals, mv)
		}
		return Multiplexed{
			Multiplexor:     SignalName(muxName),
			MultiplexValues: muxVals,
		}, nil
	default:
		return nil, protocolError(fmt.Sprintf("unknown signal presence %q", presence))
	}
}
