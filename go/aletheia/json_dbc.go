// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

// The DBC a reply carries sits at "dbc", and every refusal below names its
// place from there: a signal's field is at "dbc/messages/signals/<key>". Every
// key the kernel writes is required, and each place is read by kind only: the
// ranges and the tags are the kernel's, decided when it read the DBC and proven
// of every reply. A tag is dispatched with no refusal of its own, the last arm
// reading every tag the arms before it do not name.

// dbcPath is the DBC object's place in a reply.
const dbcPath replyPath = "dbc"

// parseDBCResponse decodes a formatDBC response into a DBCDefinition.
func parseDBCResponse(raw string) (*DBCDefinition, error) {
	m, err := decodeResponse(raw, statusSuccess)
	if err != nil {
		return nil, err
	}
	dbc, err := fieldObject(m, "", "dbc")
	if err != nil {
		return nil, err
	}
	return parseDBCDefinition(dbc)
}

// parseDBCTextResponse decodes a formatDBCText response into the .dbc text image
// plus its wfTextIssues diagnostics.  A round-trip refusal
// (handler_text_roundtrip_failed) is lifted by checkErrorStatus into a typed
// [TextRoundTripFailedError], and a size-bound refusal (input_bound_exceeded)
// into a typed [InputBoundExceededError]; those and other errors (Agda-side
// JSON parse failure on the input, unexpected status) short-circuit to the
// (*DBCText, error) tuple's error half.
func parseDBCTextResponse(raw string) (*DBCText, error) {
	m, err := decodeResponse(raw, statusSuccess)
	if err != nil {
		return nil, err
	}
	text, err := fieldString(m, "", "text")
	if err != nil {
		return nil, err
	}
	if _, err := fieldArray(m, "", "issues"); err != nil {
		return nil, err
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
	m, err := decodeResponse(raw, statusSuccess)
	if err != nil {
		return nil, err
	}
	dbcRaw, err := fieldObject(m, "", "dbc")
	if err != nil {
		return nil, err
	}
	if _, err := fieldArray(m, "", "warnings"); err != nil {
		return nil, err
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

// parseDBCDefinition decodes the DBC object of a reply, at "dbc".
func parseDBCDefinition(j map[string]any) (*DBCDefinition, error) {
	version, err := fieldString(j, dbcPath, "version")
	if err != nil {
		return nil, err
	}
	messages, err := fieldObjects(j, dbcPath, "messages", parseDBCMessage)
	if err != nil {
		return nil, err
	}
	signalGroups, err := fieldObjects(j, dbcPath, "signalGroups", parseSignalGroup)
	if err != nil {
		return nil, err
	}
	envVars, err := fieldObjects(j, dbcPath, "environmentVars", parseEnvironmentVar)
	if err != nil {
		return nil, err
	}
	valueTables, err := fieldObjects(j, dbcPath, "valueTables", parseValueTable)
	if err != nil {
		return nil, err
	}
	nodes, err := fieldObjects(j, dbcPath, "nodes", parseNode)
	if err != nil {
		return nil, err
	}
	comments, err := fieldObjects(j, dbcPath, "comments", parseComment)
	if err != nil {
		return nil, err
	}
	attributes, err := fieldObjects(j, dbcPath, "attributes", parseAttribute)
	if err != nil {
		return nil, err
	}
	unresolvedValueDescs, err := fieldObjects(j, dbcPath, "unresolvedValueDescs", parseUnresolvedValueDesc)
	if err != nil {
		return nil, err
	}

	def := &DBCDefinition{
		Version:                     version,
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

// readCANID reads the identifier of the object at path: its "extended" flag,
// then "id" at the width the flag names, whose range the kernel proves.
func readCANID(m map[string]any, path replyPath) (CANID, error) {
	extended, err := fieldBool(m, path, "extended")
	if err != nil {
		return nil, err
	}
	raw, err := fieldUint64(m, path, "id")
	if err != nil {
		return nil, err
	}
	if extended {
		return ExtendedID{value: uint32(raw)}, nil
	}
	return StandardID{value: uint16(raw)}, nil
}

// readDLC reads a message's length code from the byte count the reply writes;
// a count no code stands for, which the kernel never writes, is refused as the
// number the place does not hold.
func readDLC(m map[string]any, path replyPath) (DLC, error) {
	count, err := fieldUint64(m, path, "dlc")
	if err != nil {
		return DLC{}, err
	}
	n := int(count)
	code, ok := bytesToDlcTable[n]
	if !ok || uint64(n) != count {
		return DLC{}, replyRefusal(path.at("dlc"), expectNumber, came(m, "dlc"))
	}
	return DLC{value: code}, nil
}

// parseDBCMessage decodes one message at path, its signals included.
func parseDBCMessage(j map[string]any, path replyPath) (DBCMessage, error) {
	signals, err := fieldObjects(j, path, "signals", parseDBCSignal)
	if err != nil {
		return DBCMessage{}, err
	}
	name, err := fieldString(j, path, "name")
	if err != nil {
		return DBCMessage{}, err
	}
	id, err := readCANID(j, path)
	if err != nil {
		return DBCMessage{}, err
	}
	dlc, err := readDLC(j, path)
	if err != nil {
		return DBCMessage{}, err
	}
	sender, err := fieldString(j, path, "sender")
	if err != nil {
		return DBCMessage{}, err
	}
	senders, err := fieldStrings[NodeName](j, path, "senders")
	if err != nil {
		return DBCMessage{}, err
	}
	return NewDBCMessage(id, MessageName(name), dlc, NodeName(sender), senders, signals), nil
}

// readByteOrder reads a signal's byte order, "big_endian" its last arm.
func readByteOrder(j map[string]any, path replyPath) (ByteOrder, error) {
	name, err := fieldString(j, path, "byteOrder")
	if err != nil {
		return 0, err
	}
	switch name {
	case "little_endian":
		return LittleEndian, nil
	case "big_endian":
		fallthrough
	default:
		return BigEndian, nil
	}
}

// parseDBCSignal decodes one signal at path.
func parseDBCSignal(j map[string]any, path replyPath) (DBCSignal, error) {
	var zero DBCSignal
	name, err := fieldString(j, path, "name")
	if err != nil {
		return zero, err
	}
	startBit, err := fieldUint64(j, path, "startBit")
	if err != nil {
		return zero, err
	}
	length, err := fieldUint64(j, path, "length")
	if err != nil {
		return zero, err
	}
	byteOrder, err := readByteOrder(j, path)
	if err != nil {
		return zero, err
	}
	signed, err := fieldBool(j, path, "signed")
	if err != nil {
		return zero, err
	}
	factor, err := fieldRational(j, path, "factor")
	if err != nil {
		return zero, err
	}
	offset, err := fieldRational(j, path, "offset")
	if err != nil {
		return zero, err
	}
	minimum, err := fieldRational(j, path, "minimum")
	if err != nil {
		return zero, err
	}
	maximum, err := fieldRational(j, path, "maximum")
	if err != nil {
		return zero, err
	}
	unit, err := fieldString(j, path, "unit")
	if err != nil {
		return zero, err
	}
	receivers, err := fieldStrings[NodeName](j, path, "receivers")
	if err != nil {
		return zero, err
	}
	valueDescriptions, err := fieldObjects(j, path, "valueDescriptions", parseValueEntry)
	if err != nil {
		return zero, err
	}
	presence, err := parseSignalPresence(j, path)
	if err != nil {
		return zero, err
	}

	return DBCSignal{
		Name:              SignalName(name),
		StartBit:          BitPosition(startBit),
		BitLength:         BitLength(length),
		ByteOrder:         byteOrder,
		IsSigned:          signed,
		Factor:            factor,
		Offset:            offset,
		Minimum:           minimum,
		Maximum:           maximum,
		Unit:              Unit(unit),
		Presence:          presence,
		Receivers:         receivers,
		ValueDescriptions: valueDescriptions,
	}, nil
}

// parseSignalPresence reads the presence the kernel states for every signal,
// "multiplexed" its last arm, whose multiplexor is a string and whose selector
// values are whole numbers.
func parseSignalPresence(j map[string]any, path replyPath) (SignalPresence, error) {
	presence, err := fieldString(j, path, "presence")
	if err != nil {
		return nil, err
	}
	switch presence {
	case "always":
		return AlwaysPresent{}, nil
	case "multiplexed":
		fallthrough
	default:
		multiplexor, err := fieldString(j, path, "multiplexor")
		if err != nil {
			return nil, err
		}
		rawVals, err := fieldArray(j, path, "multiplex_values")
		if err != nil {
			return nil, err
		}
		place := path.at("multiplex_values")
		values := make([]MultiplexValue, 0, len(rawVals))
		for _, rv := range rawVals {
			v, err := readUint128(rv, place)
			if err != nil {
				return nil, err
			}
			values = append(values, v)
		}
		return Multiplexed{Multiplexor: SignalName(multiplexor), MultiplexValues: values}, nil
	}
}

// parseSignalGroup decodes one signal group: its name and its members' names.
func parseSignalGroup(g map[string]any, path replyPath) (DBCSignalGroup, error) {
	name, err := fieldString(g, path, "name")
	if err != nil {
		return DBCSignalGroup{}, err
	}
	signals, err := fieldStrings[SignalName](g, path, "signals")
	if err != nil {
		return DBCSignalGroup{}, err
	}
	return DBCSignalGroup{Name: name, Signals: signals}, nil
}

// parseEnvironmentVar decodes one environment variable, its varType the tag
// the kernel proves it to be.
func parseEnvironmentVar(ev map[string]any, path replyPath) (DBCEnvironmentVar, error) {
	name, err := fieldString(ev, path, "name")
	if err != nil {
		return DBCEnvironmentVar{}, err
	}
	varType, err := fieldUint64(ev, path, "varType")
	if err != nil {
		return DBCEnvironmentVar{}, err
	}
	initial, err := fieldRational(ev, path, "initial")
	if err != nil {
		return DBCEnvironmentVar{}, err
	}
	minimum, err := fieldRational(ev, path, "minimum")
	if err != nil {
		return DBCEnvironmentVar{}, err
	}
	maximum, err := fieldRational(ev, path, "maximum")
	if err != nil {
		return DBCEnvironmentVar{}, err
	}
	return DBCEnvironmentVar{
		Name:    name,
		VarType: DBCVarType(varType),
		Initial: initial,
		Minimum: minimum,
		Maximum: maximum,
	}, nil
}

// parseValueEntry decodes one value description: a signed key and its text.
func parseValueEntry(e map[string]any, path replyPath) (DBCValueEntry, error) {
	value, err := fieldSignMagnitude(e, path, "value")
	if err != nil {
		return DBCValueEntry{}, err
	}
	description, err := fieldString(e, path, "description")
	if err != nil {
		return DBCValueEntry{}, err
	}
	return DBCValueEntry{Value: value, Description: description}, nil
}

// parseValueTable decodes one value table: its name and its entries.
func parseValueTable(vt map[string]any, path replyPath) (DBCValueTable, error) {
	name, err := fieldString(vt, path, "name")
	if err != nil {
		return DBCValueTable{}, err
	}
	entries, err := fieldObjects(vt, path, "entries", parseValueEntry)
	if err != nil {
		return DBCValueTable{}, err
	}
	return DBCValueTable{Name: name, Entries: entries}, nil
}

// parseUnresolvedValueDesc decodes one value description the text parser
// could not attach to a signal, its CAN id read as a message's.
func parseUnresolvedValueDesc(rvd map[string]any, path replyPath) (DBCRawValueDesc, error) {
	id, err := readCANID(rvd, path)
	if err != nil {
		return DBCRawValueDesc{}, err
	}
	signalName, err := fieldString(rvd, path, "signalName")
	if err != nil {
		return DBCRawValueDesc{}, err
	}
	entries, err := fieldObjects(rvd, path, "entries", parseValueEntry)
	if err != nil {
		return DBCRawValueDesc{}, err
	}
	return DBCRawValueDesc{ID: id, SignalName: SignalName(signalName), Entries: entries}, nil
}

// --- Tier 2 parsers ---

// parseNode decodes one node.
func parseNode(n map[string]any, path replyPath) (DBCNode, error) {
	name, err := fieldString(n, path, "name")
	if err != nil {
		return DBCNode{}, err
	}
	return DBCNode{Name: NodeName(name)}, nil
}

// parseCommentTarget decodes what a comment is attached to, "envVar" its last
// arm.
func parseCommentTarget(m map[string]any, path replyPath) (DBCCommentTarget, error) {
	kind, err := fieldString(m, path, "kind")
	if err != nil {
		return nil, err
	}
	switch kind {
	case "network":
		return DBCCommentTargetNetwork{}, nil
	case "node":
		node, err := fieldString(m, path, "node")
		if err != nil {
			return nil, err
		}
		return DBCCommentTargetNode{Node: NodeName(node)}, nil
	case "message":
		id, err := readCANID(m, path)
		if err != nil {
			return nil, err
		}
		return DBCCommentTargetMessage{ID: id}, nil
	case "signal":
		id, err := readCANID(m, path)
		if err != nil {
			return nil, err
		}
		signal, err := fieldString(m, path, "signal")
		if err != nil {
			return nil, err
		}
		return DBCCommentTargetSignal{ID: id, Signal: SignalName(signal)}, nil
	case "envVar":
		fallthrough
	default:
		envVar, err := fieldString(m, path, "envVar")
		if err != nil {
			return nil, err
		}
		return DBCCommentTargetEnvVar{EnvVar: envVar}, nil
	}
}

// parseComment decodes one comment: its target and its text.
func parseComment(c map[string]any, path replyPath) (DBCComment, error) {
	target, err := fieldObjectOf(c, path, "target", parseCommentTarget)
	if err != nil {
		return DBCComment{}, err
	}
	text, err := fieldString(c, path, "text")
	if err != nil {
		return DBCComment{}, err
	}
	return DBCComment{Target: target, Text: text}, nil
}

// readAttrScope reads an attribute definition's scope, "nodeSig" its last arm.
func readAttrScope(m map[string]any, path replyPath) (DBCAttrScope, error) {
	scope, err := fieldString(m, path, "scope")
	if err != nil {
		return 0, err
	}
	switch scope {
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
		fallthrough
	default:
		return DBCAttrScopeNodeSig, nil
	}
}

// readIntBounds reads the "min" and "max" an INT or HEX definition bounds its
// values by.
func readIntBounds(m map[string]any, path replyPath) (minV, maxV int64, err error) {
	minV, err = fieldInt64(m, path, "min")
	if err != nil {
		return 0, 0, err
	}
	maxV, err = fieldInt64(m, path, "max")
	if err != nil {
		return 0, 0, err
	}
	return minV, maxV, nil
}

// parseAttrType decodes an attribute definition's type, "hex" its last arm.
func parseAttrType(m map[string]any, path replyPath) (DBCAttrType, error) {
	kind, err := fieldString(m, path, "kind")
	if err != nil {
		return nil, err
	}
	switch kind {
	case "int":
		minV, maxV, err := readIntBounds(m, path)
		if err != nil {
			return nil, err
		}
		return DBCAttrTypeInt{Min: minV, Max: maxV}, nil
	case "float":
		minV, err := fieldRational(m, path, "min")
		if err != nil {
			return nil, err
		}
		maxV, err := fieldRational(m, path, "max")
		if err != nil {
			return nil, err
		}
		return DBCAttrTypeFloat{Min: minV, Max: maxV}, nil
	case "string":
		return DBCAttrTypeString{}, nil
	case "enum":
		values, err := fieldStrings[string](m, path, "values")
		if err != nil {
			return nil, err
		}
		return DBCAttrTypeEnum{Values: values}, nil
	case "hex":
		fallthrough
	default:
		minV, maxV, err := readIntBounds(m, path)
		if err != nil {
			return nil, err
		}
		return DBCAttrTypeHex{Min: minV, Max: maxV}, nil
	}
}

// parseAttrValue decodes an attribute's value, "hex" its last arm.
func parseAttrValue(m map[string]any, path replyPath) (DBCAttrValue, error) {
	kind, err := fieldString(m, path, "kind")
	if err != nil {
		return nil, err
	}
	switch kind {
	case "int":
		v, err := fieldInt64(m, path, "value")
		if err != nil {
			return nil, err
		}
		return DBCAttrValueInt{Value: v}, nil
	case "float":
		v, err := fieldRational(m, path, "value")
		if err != nil {
			return nil, err
		}
		return DBCAttrValueFloat{Value: v}, nil
	case "string":
		v, err := fieldString(m, path, "value")
		if err != nil {
			return nil, err
		}
		return DBCAttrValueString{Value: v}, nil
	case "enum":
		v, err := fieldInt64(m, path, "value")
		if err != nil {
			return nil, err
		}
		return DBCAttrValueEnum{Value: v}, nil
	case "hex":
		fallthrough
	default:
		v, err := fieldInt64(m, path, "value")
		if err != nil {
			return nil, err
		}
		return DBCAttrValueHex{Value: v}, nil
	}
}

// parseAttrTarget decodes what an attribute is assigned to; a kind other than
// "network", "node" and "envVar" carries a CAN id, and parseAttrTargetAtID
// reads it.
func parseAttrTarget(m map[string]any, path replyPath) (DBCAttrTarget, error) {
	kind, err := fieldString(m, path, "kind")
	if err != nil {
		return nil, err
	}
	switch kind {
	case "network":
		return DBCAttrTargetNetwork{}, nil
	case "node":
		node, err := fieldString(m, path, "node")
		if err != nil {
			return nil, err
		}
		return DBCAttrTargetNode{Node: NodeName(node)}, nil
	case "envVar":
		envVar, err := fieldString(m, path, "envVar")
		if err != nil {
			return nil, err
		}
		return DBCAttrTargetEnvVar{EnvVar: envVar}, nil
	case "message", "signal", "nodeMsg", "nodeSig":
		fallthrough
	default:
		return parseAttrTargetAtID(kind, m, path)
	}
}

// parseAttrTargetAtID decodes an attribute target that carries a CAN id,
// "nodeSig" its last arm.
func parseAttrTargetAtID(kind string, m map[string]any, path replyPath) (DBCAttrTarget, error) {
	id, err := readCANID(m, path)
	if err != nil {
		return nil, err
	}
	switch kind {
	case "message":
		return DBCAttrTargetMessage{ID: id}, nil
	case "signal":
		signal, err := fieldString(m, path, "signal")
		if err != nil {
			return nil, err
		}
		return DBCAttrTargetSignal{ID: id, Signal: SignalName(signal)}, nil
	}
	node, err := fieldString(m, path, "node")
	if err != nil {
		return nil, err
	}
	if kind == "nodeMsg" {
		return DBCAttrTargetNodeMsg{Node: NodeName(node), ID: id}, nil
	}
	signal, err := fieldString(m, path, "signal")
	if err != nil {
		return nil, err
	}
	return DBCAttrTargetNodeSig{Node: NodeName(node), ID: id, Signal: SignalName(signal)}, nil
}

// parseAttribute decodes one attribute entry, "assignment" its last arm.
func parseAttribute(m map[string]any, path replyPath) (DBCAttribute, error) {
	kind, err := fieldString(m, path, "kind")
	if err != nil {
		return nil, err
	}
	name, err := fieldString(m, path, "name")
	if err != nil {
		return nil, err
	}
	switch kind {
	case "definition":
		scope, err := readAttrScope(m, path)
		if err != nil {
			return nil, err
		}
		attrType, err := fieldObjectOf(m, path, "attrType", parseAttrType)
		if err != nil {
			return nil, err
		}
		return DBCAttrDef{Name: name, Scope: scope, AttrType: attrType}, nil
	case "default":
		value, err := fieldObjectOf(m, path, "value", parseAttrValue)
		if err != nil {
			return nil, err
		}
		return DBCAttrDefault{Name: name, Value: value}, nil
	case "assignment":
		fallthrough
	default:
		target, err := fieldObjectOf(m, path, "target", parseAttrTarget)
		if err != nil {
			return nil, err
		}
		value, err := fieldObjectOf(m, path, "value", parseAttrValue)
		if err != nil {
			return nil, err
		}
		return DBCAttrAssign{Name: name, Target: target, Value: value}, nil
	}
}
