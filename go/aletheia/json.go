// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"encoding/json"
	"fmt"
	"math/big"
	"strconv"
	"unicode/utf8"
)

// --- Serialization: Go to the kernel's JSON ---

// serializeCommand builds the JSON envelope the kernel reads for a
// control-plane command. Map keys marshal in lexical order, so the same
// command is the same bytes on every run.
func serializeCommand(command string, fields map[string]any) (string, error) {
	m := map[string]any{"type": "command", "command": command}
	for k, v := range fields {
		m[k] = v
	}
	if err := refuseInvalidUTF8("command", m); err != nil {
		return "", err
	}
	b, err := json.Marshal(m)
	if err != nil {
		return "", wrapProtocolError("failed to serialize command", err)
	}
	return string(b), nil
}

// refuseInvalidUTF8 walks a value about to be encoded and refuses any string
// that is not valid UTF-8, naming where it sits. The encoder would otherwise
// replace each bad byte with U+FFFD and send the altered string, so a caller
// would learn nothing and the kernel would act on something else. The peer
// bindings refuse the same input: Python raises encoding the command, C++
// throws from its JSON writer, and a Rust string cannot hold the bytes at all.
func refuseInvalidUTF8(path string, v any) error {
	switch x := v.(type) {
	case string:
		if !utf8.ValidString(x) {
			return validationError(path + " is not valid UTF-8")
		}
	case json.RawMessage:
		if !utf8.Valid(x) {
			return validationError(path + " is not valid UTF-8")
		}
	case map[string]any:
		for k, item := range x {
			if !utf8.ValidString(k) {
				return validationError(path + ": a key is not valid UTF-8")
			}
			if err := refuseInvalidUTF8(path+"."+k, item); err != nil {
				return err
			}
		}
	case []any:
		for i, item := range x {
			if err := refuseInvalidUTF8(fmt.Sprintf("%s[%d]", path, i), item); err != nil {
				return err
			}
		}
	case []string:
		for i, item := range x {
			if !utf8.ValidString(item) {
				return validationError(fmt.Sprintf("%s[%d] is not valid UTF-8", path, i))
			}
		}
	case []map[string]any:
		for i, item := range x {
			if err := refuseInvalidUTF8(fmt.Sprintf("%s[%d]", path, i), item); err != nil {
				return err
			}
		}
	}
	return nil
}

// MarshalJSON renders the DBC as the canonical wire JSON the kernel emits,
// lowercase keys and exact rationals, rather than the field names Go would
// use, so json.Marshal of a definition is the form every binding reads. It is
// the encoder half alone: a definition is loaded through ParseDBC or
// ParseDBCText, so there is no canonical UnmarshalJSON beside it.
func (d DBCDefinition) MarshalJSON() ([]byte, error) {
	raw, err := serializeDBC(d)
	if err != nil {
		return nil, err
	}
	return raw, nil
}

// serializeDBC is the definition as the bytes the kernel reads under the dbc
// field of a command. Callers embed the bytes as they are, so a command
// carrying a definition marshals it once.
//
// The one marshal doubles as the size check: the bytes are measured against
// the text cap before they leave. The parser refuses an oversized input
// first, so nothing reaching here should be over it, which is the point of
// measuring anyway.
func serializeDBC(dbc DBCDefinition) (json.RawMessage, error) {
	msgs := make([]map[string]any, 0, len(dbc.Messages))
	for _, msg := range dbc.Messages {
		sigs := make([]map[string]any, 0, len(msg.Signals))
		for _, sig := range msg.Signals {
			receivers := sig.Receivers
			if receivers == nil {
				receivers = []NodeName{}
			}
			valueDescs := make([]map[string]any, 0, len(sig.ValueDescriptions))
			for _, e := range sig.ValueDescriptions {
				valueDescs = append(valueDescs, map[string]any{
					"value":       e.Value,
					"description": e.Description,
				})
			}
			s := map[string]any{
				"name":              string(sig.Name),
				"startBit":          sig.StartBit,
				"length":            sig.BitLength,
				"signed":            sig.IsSigned,
				"factor":            serializeRational(sig.Factor),
				"offset":            serializeRational(sig.Offset),
				"minimum":           serializeRational(sig.Minimum),
				"maximum":           serializeRational(sig.Maximum),
				"unit":              string(sig.Unit),
				"receivers":         receivers,
				"valueDescriptions": valueDescs,
			}
			order, err := byteOrderWireName(sig.ByteOrder)
			if err != nil {
				return nil, err
			}
			s["byteOrder"] = order
			// Emit explicit "presence"
			// discriminator on multiplexed signals (mirrors Always
			// signals' "presence": "always").  Cross-binding parity
			// with the Agda Formatter and the Python TypedDict.
			if mux, ok := sig.Presence.(Multiplexed); ok {
				s["presence"] = "multiplexed"
				s["multiplexor"] = string(mux.Multiplexor)
				vals := make([]uint32, len(mux.MultiplexValues))
				for i, v := range mux.MultiplexValues {
					vals[i] = uint32(v)
				}
				s["multiplex_values"] = vals
			} else {
				s["presence"] = "always"
			}
			sigs = append(sigs, s)
		}
		senders := msg.Senders
		if senders == nil {
			senders = []NodeName{}
		}
		// The extended flag is written only when it is true, which is the shape
		// the kernel writes and every binding reads.
		m := map[string]any{
			"name":    string(msg.Name),
			"dlc":     msg.DLC.ToBytes(),
			"sender":  string(msg.Sender),
			"senders": senders,
			"signals": sigs,
		}
		if _, err := withCANID(m, msg.ID); err != nil {
			return nil, wrapValidationError(fmt.Sprintf("message %q", msg.Name), err)
		}
		msgs = append(msgs, m)
	}

	groups := make([]map[string]any, 0, len(dbc.SignalGroups))
	for _, g := range dbc.SignalGroups {
		sigs := make([]string, len(g.Signals))
		for i, s := range g.Signals {
			sigs[i] = string(s)
		}
		groups = append(groups, map[string]any{"name": g.Name, "signals": sigs})
	}

	envVars := make([]map[string]any, 0, len(dbc.EnvironmentVars))
	for _, ev := range dbc.EnvironmentVars {
		envVars = append(envVars, map[string]any{
			"name":    ev.Name,
			"varType": int(ev.VarType),
			"initial": serializeRational(ev.Initial),
			"minimum": serializeRational(ev.Minimum),
			"maximum": serializeRational(ev.Maximum),
		})
	}

	valueTables := make([]map[string]any, 0, len(dbc.ValueTables))
	for _, vt := range dbc.ValueTables {
		entries := make([]map[string]any, 0, len(vt.Entries))
		for _, e := range vt.Entries {
			entries = append(entries, map[string]any{
				"value":       e.Value,
				"description": e.Description,
			})
		}
		valueTables = append(valueTables, map[string]any{"name": vt.Name, "entries": entries})
	}

	nodes := make([]map[string]any, 0, len(dbc.Nodes))
	for _, n := range dbc.Nodes {
		nodes = append(nodes, map[string]any{"name": n.Name})
	}

	comments := make([]map[string]any, 0, len(dbc.Comments))
	for _, c := range dbc.Comments {
		target, err := serializeCommentTarget(c.Target)
		if err != nil {
			return nil, err
		}
		comments = append(comments, map[string]any{"target": target, "text": c.Text})
	}

	attributes := make([]map[string]any, 0, len(dbc.Attributes))
	for _, a := range dbc.Attributes {
		obj, err := serializeAttribute(a)
		if err != nil {
			return nil, err
		}
		attributes = append(attributes, obj)
	}

	// The value descriptions the text parser could not attach to a signal: the
	// identifier pair, then the signal name and the entries.
	unresolvedValueDescs := make([]map[string]any, 0, len(dbc.UnresolvedValueDescriptions))
	for _, rvd := range dbc.UnresolvedValueDescriptions {
		entries := make([]map[string]any, 0, len(rvd.Entries))
		for _, e := range rvd.Entries {
			entries = append(entries, map[string]any{
				"value":       e.Value,
				"description": e.Description,
			})
		}
		obj := map[string]any{
			"signalName": rvd.SignalName,
			"entries":    entries,
		}
		if _, err := withCANID(obj, rvd.ID); err != nil {
			return nil, wrapValidationError(fmt.Sprintf("unresolved value description of %q", rvd.SignalName), err)
		}
		unresolvedValueDescs = append(unresolvedValueDescs, obj)
	}

	out := map[string]any{
		"version":              dbc.Version,
		"messages":             msgs,
		"signalGroups":         groups,
		"environmentVars":      envVars,
		"valueTables":          valueTables,
		"nodes":                nodes,
		"comments":             comments,
		"attributes":           attributes,
		"unresolvedValueDescs": unresolvedValueDescs,
	}
	// The definition is checked before it is encoded, not after: the encoder
	// would have replaced a bad byte, and the bytes it returned would then be
	// valid UTF-8 carrying a name the caller never wrote.
	if err := refuseInvalidUTF8("dbc", out); err != nil {
		return nil, err
	}
	// The one marshal is both the answer and the size check.
	b, err := json.Marshal(out)
	if err != nil {
		return nil, wrapProtocolError("failed to size-check DBC", err)
	}
	if err := refuseOversize(uint64(len(b)), MaxDBCTextBytes); err != nil {
		return nil, err
	}
	return json.RawMessage(b), nil
}

// byteOrderWireName is a byte order as the wire spells it, which is the name
// String() renders from the constant's own line comment. Reading a byte order
// back compares against the same two names, so the printed form and the wire
// form cannot drift apart.
func byteOrderWireName(b ByteOrder) (string, error) {
	switch b {
	case LittleEndian, BigEndian:
		return b.String(), nil
	default:
		return "", validationError(fmt.Sprintf("invalid byte order %d", b))
	}
}

// --- Tier 2 serializers (Go to the kernel's JSON) ---

// withCANID adds an identifier to m the way the kernel's formatter writes one:
// the number always, the extended flag only when it is set. An identifier left
// unset, nil in its interface, is refused rather than dereferenced.
func withCANID(m map[string]any, id CANID) (map[string]any, error) {
	if id == nil {
		return nil, validationError("a CAN identifier is unset")
	}
	m["id"] = id.Value()
	if id.IsExtended() {
		m["extended"] = true
	}
	return m, nil
}

func serializeCommentTarget(t DBCCommentTarget) (map[string]any, error) {
	switch v := t.(type) {
	case DBCCommentTargetNetwork:
		return map[string]any{"kind": "network"}, nil
	case DBCCommentTargetNode:
		return map[string]any{"kind": "node", "node": v.Node}, nil
	case DBCCommentTargetMessage:
		return withCANID(map[string]any{"kind": "message"}, v.ID)
	case DBCCommentTargetSignal:
		return withCANID(map[string]any{"kind": "signal", "signal": v.Signal}, v.ID)
	case DBCCommentTargetEnvVar:
		return map[string]any{"kind": "envVar", "envVar": v.EnvVar}, nil
	default:
		return nil, validationError(fmt.Sprintf("unsupported comment target type %T", t))
	}
}

func serializeAttrScope(s DBCAttrScope) (string, error) {
	switch s {
	case DBCAttrScopeNetwork:
		return "network", nil
	case DBCAttrScopeNode:
		return "node", nil
	case DBCAttrScopeMessage:
		return "message", nil
	case DBCAttrScopeSignal:
		return "signal", nil
	case DBCAttrScopeEnvVar:
		return "envVar", nil
	case DBCAttrScopeNodeMsg:
		return "nodeMsg", nil
	case DBCAttrScopeNodeSig:
		return "nodeSig", nil
	default:
		return "", validationError(fmt.Sprintf("invalid attr scope %d", s))
	}
}

func serializeAttrType(t DBCAttrType) (map[string]any, error) {
	switch v := t.(type) {
	case DBCAttrTypeInt:
		return map[string]any{"kind": "int", "min": v.Min, "max": v.Max}, nil
	case DBCAttrTypeFloat:
		return map[string]any{
			"kind": "float",
			"min":  serializeRational(v.Min),
			"max":  serializeRational(v.Max),
		}, nil
	case DBCAttrTypeString:
		return map[string]any{"kind": "string"}, nil
	case DBCAttrTypeEnum:
		values := make([]string, len(v.Values))
		copy(values, v.Values)
		return map[string]any{"kind": "enum", "values": values}, nil
	case DBCAttrTypeHex:
		return map[string]any{"kind": "hex", "min": v.Min, "max": v.Max}, nil
	default:
		return nil, validationError(fmt.Sprintf("unsupported attr type %T", t))
	}
}

func serializeAttrValue(v DBCAttrValue) (map[string]any, error) {
	switch a := v.(type) {
	case DBCAttrValueInt:
		return map[string]any{"kind": "int", "value": a.Value}, nil
	case DBCAttrValueFloat:
		return map[string]any{"kind": "float", "value": serializeRational(a.Value)}, nil
	case DBCAttrValueString:
		return map[string]any{"kind": "string", "value": a.Value}, nil
	case DBCAttrValueEnum:
		return map[string]any{"kind": "enum", "value": a.Value}, nil
	case DBCAttrValueHex:
		return map[string]any{"kind": "hex", "value": a.Value}, nil
	default:
		return nil, validationError(fmt.Sprintf("unsupported attr value type %T", v))
	}
}

func serializeAttrTarget(t DBCAttrTarget) (map[string]any, error) {
	switch v := t.(type) {
	case DBCAttrTargetNetwork:
		return map[string]any{"kind": "network"}, nil
	case DBCAttrTargetNode:
		return map[string]any{"kind": "node", "node": v.Node}, nil
	case DBCAttrTargetMessage:
		return withCANID(map[string]any{"kind": "message"}, v.ID)
	case DBCAttrTargetSignal:
		return withCANID(map[string]any{"kind": "signal", "signal": v.Signal}, v.ID)
	case DBCAttrTargetEnvVar:
		return map[string]any{"kind": "envVar", "envVar": v.EnvVar}, nil
	case DBCAttrTargetNodeMsg:
		return withCANID(map[string]any{"kind": "nodeMsg", "node": v.Node}, v.ID)
	case DBCAttrTargetNodeSig:
		return withCANID(map[string]any{"kind": "nodeSig", "node": v.Node, "signal": v.Signal}, v.ID)
	default:
		return nil, validationError(fmt.Sprintf("unsupported attr target type %T", t))
	}
}

func serializeAttribute(a DBCAttribute) (map[string]any, error) {
	switch v := a.(type) {
	case DBCAttrDef:
		scope, err := serializeAttrScope(v.Scope)
		if err != nil {
			return nil, err
		}
		at, err := serializeAttrType(v.AttrType)
		if err != nil {
			return nil, err
		}
		return map[string]any{
			"kind":     "definition",
			"name":     v.Name,
			"scope":    scope,
			"attrType": at,
		}, nil
	case DBCAttrDefault:
		val, err := serializeAttrValue(v.Value)
		if err != nil {
			return nil, err
		}
		return map[string]any{"kind": "default", "name": v.Name, "value": val}, nil
	case DBCAttrAssign:
		target, err := serializeAttrTarget(v.Target)
		if err != nil {
			return nil, err
		}
		val, err := serializeAttrValue(v.Value)
		if err != nil {
			return nil, err
		}
		return map[string]any{
			"kind":   "assignment",
			"name":   v.Name,
			"target": target,
			"value":  val,
		}, nil
	default:
		return nil, validationError(fmt.Sprintf("unsupported attribute type %T", a))
	}
}

// validateRational refuses a rational the wire cannot carry, which is one
// whose denominator is zero or negative. A [Rational] is a pair of integers,
// so there is nothing else to refuse: no value of it is infinite or undefined.
func validateRational(name string, r Rational) error {
	if r.Denominator <= 0 {
		return validationError(fmt.Sprintf("%s: non-positive denominator %d (must be > 0)",
			name, r.Denominator))
	}
	return nil
}

// ratCmp compares two rationals with positive denominators by their
// cross-products, answering as [big.Int.Cmp] does. The products are taken at
// arbitrary width: at int64 they would wrap, and a numerator near the maximum
// would compare as the smaller value.
func ratCmp(r1, r2 Rational) int {
	a := new(big.Int).Mul(big.NewInt(r1.Numerator), big.NewInt(r2.Denominator))
	b := new(big.Int).Mul(big.NewInt(r2.Numerator), big.NewInt(r1.Denominator))
	return a.Cmp(b)
}

// ratPredicate is a predicate over one signal carrying one rational under the
// field name the wire gives it. The rational is refused here rather than at
// the kernel, since a denominator the wire cannot represent is the caller's
// mistake and the message names which field it was.
func ratPredicate(kind string, signal SignalName, field string, value Rational) (map[string]any, error) {
	if err := validateRational(kind+"."+field, value); err != nil {
		return nil, err
	}
	return map[string]any{
		"predicate": kind,
		"signal":    string(signal),
		field:       serializeRational(value),
	}, nil
}

// serializePredicate encodes a predicate in the shape the kernel's LTL parser
// reads.
func serializePredicate(p Predicate) (map[string]any, error) {
	switch p := p.(type) {
	case Equals:
		return ratPredicate("equals", p.Signal, "value", p.Value)
	case LessThan:
		return ratPredicate("lessThan", p.Signal, "value", p.Value)
	case GreaterThan:
		return ratPredicate("greaterThan", p.Signal, "value", p.Value)
	case LessThanOrEqual:
		return ratPredicate("lessThanOrEqual", p.Signal, "value", p.Value)
	case GreaterThanOrEqual:
		return ratPredicate("greaterThanOrEqual", p.Signal, "value", p.Value)
	case ChangedBy:
		return ratPredicate("changedBy", p.Signal, "delta", p.Delta)
	case Between:
		out, err := ratPredicate("between", p.Signal, "min", p.Min)
		if err != nil {
			return nil, err
		}
		if err := validateRational("between.max", p.Max); err != nil {
			return nil, err
		}
		if ratCmp(p.Max, p.Min) < 0 {
			return nil, validationError(fmt.Sprintf("between: min (%s) exceeds max (%s)",
				formatRationalExact(p.Min), formatRationalExact(p.Max)))
		}
		out["max"] = serializeRational(p.Max)
		return out, nil
	case StableWithin:
		out, err := ratPredicate("stableWithin", p.Signal, "tolerance", p.Tolerance)
		if err != nil {
			return nil, err
		}
		if p.Tolerance.Numerator < 0 {
			return nil, validationError(fmt.Sprintf("negative tolerance: %s",
				formatRationalExact(p.Tolerance)))
		}
		return out, nil
	default:
		return nil, validationError(fmt.Sprintf("unsupported predicate type %T", p))
	}
}

// validateTimeBound rejects TimeBounds the Agda core cannot represent
// (negative microseconds).
func validateTimeBound(t TimeBound) error {
	if t.Microseconds < 0 {
		return validationError(fmt.Sprintf("negative time bound: %d microseconds", t.Microseconds))
	}
	return nil
}

// serializeFormula encodes a formula for the kernel, bounded in depth so that
// input nested past what any real property needs fails rather than growing the
// stack.
func serializeFormula(f Formula) (map[string]any, error) {
	return serializeFormulaDepth(f, 0)
}

// unaryOp is an operator over one formula.
func unaryOp(op string, inner Formula, depth int) (map[string]any, error) {
	f, err := serializeFormulaDepth(inner, depth+1)
	if err != nil {
		return nil, err
	}
	return map[string]any{"operator": op, "formula": f}, nil
}

// binaryOp is an operator over two.
func binaryOp(op string, left, right Formula, depth int) (map[string]any, error) {
	l, err := serializeFormulaDepth(left, depth+1)
	if err != nil {
		return nil, err
	}
	r, err := serializeFormulaDepth(right, depth+1)
	if err != nil {
		return nil, err
	}
	return map[string]any{"operator": op, "left": l, "right": r}, nil
}

// metricOp adds the time bound the metric operators carry, refusing a bound
// the kernel has no representation for.
func metricOp(bound TimeBound, build func() (map[string]any, error)) (map[string]any, error) {
	if err := validateTimeBound(bound); err != nil {
		return nil, err
	}
	m, err := build()
	if err != nil {
		return nil, err
	}
	m["timebound"] = bound.Microseconds
	return m, nil
}

// serializeFormulaDepth carries the remaining depth budget through the tree.
func serializeFormulaDepth(f Formula, depth int) (map[string]any, error) {
	if depth > maxFormulaDepth {
		return nil, validationError(fmt.Sprintf("formula nesting depth exceeds %d", maxFormulaDepth))
	}
	switch f := f.(type) {
	case Atomic:
		pred, err := serializePredicate(f.Predicate)
		if err != nil {
			return nil, err
		}
		return map[string]any{"operator": "atomic", "predicate": pred}, nil
	case Not:
		return unaryOp("not", f.Inner, depth)
	case Next:
		return unaryOp("next", f.Inner, depth)
	case WeakNext:
		return unaryOp("weakNext", f.Inner, depth)
	case Always:
		return unaryOp("always", f.Inner, depth)
	case Eventually:
		return unaryOp("eventually", f.Inner, depth)
	case And:
		return binaryOp("and", f.Left, f.Right, depth)
	case Or:
		return binaryOp("or", f.Left, f.Right, depth)
	case Until:
		return binaryOp("until", f.Left, f.Right, depth)
	case Release:
		return binaryOp("release", f.Left, f.Right, depth)
	case MetricAlways:
		return metricOp(f.Bound, func() (map[string]any, error) { return unaryOp("metricAlways", f.Inner, depth) })
	case MetricEventually:
		return metricOp(f.Bound, func() (map[string]any, error) { return unaryOp("metricEventually", f.Inner, depth) })
	case MetricUntil:
		return metricOp(f.Bound, func() (map[string]any, error) { return binaryOp("metricUntil", f.Left, f.Right, depth) })
	case MetricRelease:
		return metricOp(f.Bound, func() (map[string]any, error) { return binaryOp("metricRelease", f.Left, f.Right, depth) })
	default:
		return nil, validationError(fmt.Sprintf("unsupported formula type %T", f))
	}
}

// --- Rational helpers ---

// parseRational reads a Rational from a JSON scalar (number) or the
// {"numerator","denominator"} object shape, matching Python's Fraction
// decoding path.
func parseRational(v any) (Rational, error) {
	switch n := v.(type) {
	case json.Number:
		// A scalar number is the integer rational n/1.
		i, cls := decodeJSONInt(v)
		// The value is a number here, so only the fractional and the
		// out-of-range answers can come back.
		switch cls {
		case intParseFractional:
			return Rational{}, protocolError(fmt.Sprintf("expected integer rational, got fractional: %v", v))
		case intParseOverflow:
			return Rational{}, protocolError(fmt.Sprintf("rational out of int64 range: %v", v))
		}
		return Rational{Numerator: i, Denominator: 1}, nil
	case map[string]any:
		num, den, err := rationalParts(n)
		if err != nil {
			return Rational{}, err
		}
		return Rational{Numerator: num, Denominator: den}, nil
	default:
		return Rational{}, protocolError(fmt.Sprintf("expected number or rational dict, got %T", v))
	}
}

// rationalParts reads the two components of a wire rational, refusing every
// shape the wire does not carry: a component missing or not a number (a missing
// key reads as nil, which is not a number), one with a fractional part, one
// outside int64, and a denominator of zero or less. A negative denominator is
// refused rather than rewritten, since the kernel and the Python decoder both
// refuse it and rewriting here would let a shape through Go that no other
// binding accepts.
func rationalParts(m map[string]any) (int64, int64, error) {
	rawNum, rawDen := m["numerator"], m["denominator"]
	num, numCls := decodeJSONInt(rawNum)
	den, denCls := decodeJSONInt(rawDen)
	if numCls == intParseNotNumber || denCls == intParseNotNumber {
		return 0, 0, protocolError(fmt.Sprintf("rational needs a numeric numerator and denominator, got %v", m))
	}
	// The components are checked for being integers before anything is read
	// from them, so a fractional denominator is not reported as a zero one and
	// a fractional numerator is never truncated.
	if numCls == intParseFractional || denCls == intParseFractional {
		return 0, 0, protocolError(fmt.Sprintf("expected integer rational, got %v/%v", rawNum, rawDen))
	}
	if numCls == intParseOverflow || denCls == intParseOverflow {
		return 0, 0, protocolError(fmt.Sprintf("rational components out of int64 range: %v/%v", rawNum, rawDen))
	}
	if den <= 0 {
		return 0, 0, protocolError(fmt.Sprintf("non-positive denominator in rational: %v", m))
	}
	return num, den, nil
}

// serializeRational emits a rational as its two components, so the wire keeps
// the exact value rather than a rounded one.
func serializeRational(r Rational) any {
	if r.Denominator == 1 {
		return r.Numerator
	}
	return map[string]any{"numerator": r.Numerator, "denominator": r.Denominator}
}

// formatRationalExact renders a rational for a refusal message: through the
// kernel when its runtime is up, which is the form every binding prints, and
// as a bare fraction otherwise. Predicate validation runs before the runtime
// need be up, so this never fails and never rounds.
func formatRationalExact(r Rational) string {
	if s, err := formatRational(r); err == nil {
		return s
	}
	if r.Denominator == 1 {
		return strconv.FormatInt(r.Numerator, 10)
	}
	return strconv.FormatInt(r.Numerator, 10) + "/" + strconv.FormatInt(r.Denominator, 10)
}
