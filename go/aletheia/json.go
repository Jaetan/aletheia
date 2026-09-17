// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"encoding/binary"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"math"
	"math/big"
	"strconv"
	"strings"
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
				receivers = []string{}
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
			senders = []string{}
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
		attachCANID(m, msg.ID.Value(), msg.ID.IsExtended())
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
		attachCANID(obj, rvd.ID.Value(), rvd.ID.IsExtended())
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
	if size := uint64(len(b)); size > MaxDBCTextBytes {
		return nil, newInputBoundExceededError(BoundKindInputLengthBytes, size, MaxDBCTextBytes, CodeInputBoundExceeded)
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

// attachCANID writes an identifier the way the kernel's formatter does: the
// number always, the extended flag only when it is set.
func attachCANID(m map[string]any, id uint32, extended bool) {
	m["id"] = id
	if extended {
		m["extended"] = true
	}
}

func serializeCommentTarget(t DBCCommentTarget) (map[string]any, error) {
	switch v := t.(type) {
	case DBCCommentTargetNetwork:
		return map[string]any{"kind": "network"}, nil
	case DBCCommentTargetNode:
		return map[string]any{"kind": "node", "node": v.Node}, nil
	case DBCCommentTargetMessage:
		out := map[string]any{"kind": "message"}
		attachCANID(out, v.ID, v.Extended)
		return out, nil
	case DBCCommentTargetSignal:
		out := map[string]any{"kind": "signal"}
		attachCANID(out, v.ID, v.Extended)
		out["signal"] = v.Signal
		return out, nil
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
		out := map[string]any{"kind": "message"}
		attachCANID(out, v.ID, v.Extended)
		return out, nil
	case DBCAttrTargetSignal:
		out := map[string]any{"kind": "signal"}
		attachCANID(out, v.ID, v.Extended)
		out["signal"] = v.Signal
		return out, nil
	case DBCAttrTargetEnvVar:
		return map[string]any{"kind": "envVar", "envVar": v.EnvVar}, nil
	case DBCAttrTargetNodeMsg:
		out := map[string]any{"kind": "nodeMsg", "node": v.Node}
		attachCANID(out, v.ID, v.Extended)
		return out, nil
	case DBCAttrTargetNodeSig:
		out := map[string]any{"kind": "nodeSig", "node": v.Node}
		attachCANID(out, v.ID, v.Extended)
		out["signal"] = v.Signal
		return out, nil
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

// rationalLess compares two rationals by their cross-products, both
// denominators being positive, which validateRational has established. The
// products are taken at arbitrary width: at int64 they would wrap, and a
// numerator near the maximum would compare as the smaller value.
func rationalLess(r1, r2 Rational) bool {
	a := new(big.Int).Mul(big.NewInt(r1.Numerator), big.NewInt(r2.Denominator))
	b := new(big.Int).Mul(big.NewInt(r2.Numerator), big.NewInt(r1.Denominator))
	return a.Cmp(b) < 0
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
		if rationalLess(p.Max, p.Min) {
			return nil, validationError(fmt.Sprintf("between: min (%s) exceeds max (%s)",
				formatRationalExact(p.Min), formatRationalExact(p.Max)))
		}
		out["max"] = serializeRational(p.Max)
		return out, nil
	case StableWithin:
		if err := validateRational("stableWithin.tolerance", p.Tolerance); err != nil {
			return nil, err
		}
		if p.Tolerance.Numerator < 0 {
			return nil, validationError(fmt.Sprintf("negative tolerance: %s",
				formatRationalExact(p.Tolerance)))
		}
		return ratPredicate("stableWithin", p.Signal, "tolerance", p.Tolerance)
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
// shape the wire does not carry: a component missing or not a number, one with
// a fractional part, one outside int64, a zero denominator, and a negative
// one. A negative denominator is refused rather than rewritten, since the
// kernel and the Python decoder both refuse it and rewriting here would let a
// shape through Go that no other binding accepts.
func rationalParts(m map[string]any) (int64, int64, error) {
	rawNum, okNum := m["numerator"]
	rawDen, okDen := m["denominator"]
	num, numCls := decodeJSONInt(rawNum)
	den, denCls := decodeJSONInt(rawDen)
	if !okNum || !okDen || numCls == intParseNotNumber || denCls == intParseNotNumber {
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
	if den == 0 {
		return 0, 0, protocolError(fmt.Sprintf("zero denominator in rational: %v", m))
	}
	if den < 0 {
		return 0, 0, protocolError(fmt.Sprintf("negative denominator in rational: %v", m))
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
// as a bare fraction otherwise. Predicate validation runs before any backend
// exists, so this never fails and never rounds.
func formatRationalExact(r Rational) string {
	if s, err := formatRational(r); err == nil {
		return s
	}
	if r.Denominator == 1 {
		return strconv.FormatInt(r.Numerator, 10)
	}
	return strconv.FormatInt(r.Numerator, 10) + "/" + strconv.FormatInt(r.Denominator, 10)
}

// --- Deserialization: the kernel's JSON to Go ---

// intParse classifies the outcome of decoding a JSON number as an int64.
type intParse int

const (
	intParseOK         intParse = iota // an exact int64
	intParseNotNumber                  // not a JSON number at all
	intParseFractional                 // numeric, but has a fractional part
	intParseOverflow                   // integer-valued, but outside int64
)

// decodeJSONInt reads a wire number as an exact int64. There is no float64
// arm on purpose: a value that is not a json.Number did not come off the wire
// through parseResponse, and taking it would put every integer through a
// float's 53 bits of mantissa.
func decodeJSONInt(v any) (int64, intParse) {
	switch n := v.(type) {
	case json.Number:
		i, err := strconv.ParseInt(n.String(), 10, 64)
		if err == nil {
			return i, intParseOK
		}
		// A fractional, exponent or out-of-range literal is refused. The kernel
		// writes plain integers, which the other bindings' readers also require,
		// so nothing is lost by refusing the rest.
		if errors.Is(err, strconv.ErrRange) {
			return 0, intParseOverflow
		}
		return 0, intParseFractional
	default:
		return 0, intParseNotNumber
	}
}

// parseNumberAsInt64 reads an exact int64 from a wire number, or from a
// rational that divides evenly.
func parseNumberAsInt64(v any) (int64, error) {
	switch n := v.(type) {
	case json.Number:
		i, cls := decodeJSONInt(v)
		// The value is a number here, so only the fractional and the
		// out-of-range answers can come back.
		switch cls {
		case intParseFractional:
			return 0, protocolError(fmt.Sprintf("expected integer, got fractional: %v", v))
		case intParseOverflow:
			return 0, protocolError(fmt.Sprintf("integer out of int64 range: %v", v))
		}
		return i, nil
	case map[string]any:
		num, den, err := rationalParts(n)
		if err != nil {
			return 0, err
		}
		if num%den != 0 {
			return 0, protocolError(fmt.Sprintf("expected integer, got non-exact rational %d/%d", num, den))
		}
		return num / den, nil
	default:
		return 0, protocolError(fmt.Sprintf("expected integer, got %T: %v", v, v))
	}
}

// getString returns the string value for key, or "" if missing or wrong type.
func getString(m map[string]any, key string) string {
	if v, ok := m[key]; ok {
		if s, ok := v.(string); ok {
			return s
		}
	}
	return ""
}

// getBool returns the bool value for key, or false if missing or wrong type.
func getBool(m map[string]any, key string) bool {
	if v, ok := m[key]; ok {
		if b, ok := v.(bool); ok {
			return b
		}
	}
	return false
}

// getArray returns the []any value for key, or nil if missing or wrong type.
func getArray(m map[string]any, key string) []any {
	if v, ok := m[key]; ok {
		if a, ok := v.([]any); ok {
			return a
		}
	}
	return nil
}

// getObject returns the map[string]any value for key, or nil if missing or wrong type.
func getObject(m map[string]any, key string) map[string]any {
	if v, ok := m[key]; ok {
		if o, ok := v.(map[string]any); ok {
			return o
		}
	}
	return nil
}

// parseResponse reads a kernel response into a generic map, which the typed
// decoders below narrow.
//
// Numbers arrive as decimal strings rather than float64, so a numerator or
// denominator above two to the fifty-third survives; the three numeric helpers
// read them exactly. A decoder accepts trailing bytes where json.Unmarshal
// refuses them, so the refusal is made here: a response is one JSON value.
func parseResponse(raw string) (map[string]any, error) {
	dec := json.NewDecoder(strings.NewReader(raw))
	dec.UseNumber()
	var m map[string]any
	if err := dec.Decode(&m); err != nil {
		return nil, wrapProtocolError("invalid JSON response", err)
	}
	if err := dec.Decode(new(json.RawMessage)); err == nil {
		return nil, protocolError("unexpected trailing data after JSON response")
	} else if !errors.Is(err, io.EOF) {
		return nil, wrapProtocolError("invalid trailing data after JSON response", err)
	}
	return m, nil
}

// decodeResponse reads a response, lifts an error envelope into its typed
// error, and holds the status to the one the caller expects. Every typed
// decoder below opens with it, so a response that is malformed, an error, or
// simply not the answer to the command asked is refused in one place.
func decodeResponse(raw, wantStatus string) (map[string]any, error) {
	m, err := parseResponse(raw)
	if err != nil {
		return nil, err
	}
	if err := checkErrorStatus(m); err != nil {
		return nil, err
	}
	if status := getString(m, "status"); status != wantStatus {
		return nil, protocolError(fmt.Sprintf("expected %s response, got status: %q", wantStatus, status))
	}
	return m, nil
}

// requireString reads a field that must be there. An error response carries
// its code and its message, so a default in place of either would hide drift
// between the binding and the kernel rather than report it. The Python decoder
// requires the same two in build_error_response.
func requireString(m map[string]any, key string) (string, error) {
	v, ok := m[key]
	if !ok {
		return "", protocolError(fmt.Sprintf(
			"Error response missing or non-string '%s' field; got <absent>", key))
	}
	s, ok := v.(string)
	if !ok {
		return "", protocolError(fmt.Sprintf(
			"Error response missing or non-string '%s' field; got %T", key, v))
	}
	return s, nil
}

// The three lifts below turn a coded error response into the typed error a
// caller can match on, and each answers nil when its payload is incomplete, so
// the caller falls back to the generic coded error and the decode never fails
// harder than it would have. C++ and Python degrade the same way.

// inputBoundExceededFromResponse lifts a bound refusal, whichever bound the
// kernel crossed. The wire message is not carried: the typed error renders an
// equivalent one from the kind, the observed size and the limit, as each
// binding renders it in its own idiom.
func inputBoundExceededFromResponse(code string, m map[string]any) *InputBoundExceededError {
	if code != CodeInputBoundExceeded {
		return nil
	}
	kind, ok := m["bound_kind"].(string)
	if !ok {
		return nil
	}
	observed, ok := jsonNumberToUint64(m["observed"])
	if !ok {
		return nil
	}
	limit, ok := jsonNumberToUint64(m["limit"])
	if !ok {
		return nil
	}
	return newInputBoundExceededError(kind, observed, limit, code)
}

// jsonNumberToUint64 reads a wire number as an exact uint64, refusing a
// negative, a fractional, an exponent form and anything too large.
func jsonNumberToUint64(v any) (uint64, bool) {
	switch n := v.(type) {
	case json.Number:
		i, err := strconv.ParseUint(n.String(), 10, 64)
		if err != nil {
			return 0, false
		}
		return i, true
	default:
		return 0, false
	}
}

// validationFailedFromResponse lifts a refusal of a DBC that failed
// validation. The issues have the element shape of a validation response, so
// parseIssueArray decodes them; their presence is checked first, since a
// missing key would otherwise read as an empty array. The wire message is
// carried through, so the rendered error is what the generic one rendered.
func validationFailedFromResponse(code, msg string, m map[string]any) *ValidationFailedError {
	if code != CodeHandlerValidationFailed {
		return nil
	}
	hasErrors, ok := m["has_errors"].(bool)
	if !ok {
		return nil
	}
	if _, ok := m["issues"].([]any); !ok {
		return nil
	}
	issues, err := parseIssueArray(m, "issues")
	if err != nil {
		return nil
	}
	return newValidationFailedError(issues, hasErrors, code, msg)
}

// textRoundtripFailedFromResponse lifts a refusal of a DBC whose text does not
// re-parse, carrying the same payload as the validation refusal above.
func textRoundtripFailedFromResponse(code, msg string, m map[string]any) *TextRoundTripFailedError {
	if code != CodeHandlerTextRoundtripFailed {
		return nil
	}
	hasErrors, ok := m["has_errors"].(bool)
	if !ok {
		return nil
	}
	if _, ok := m["issues"].([]any); !ok {
		return nil
	}
	issues, err := parseIssueArray(m, "issues")
	if err != nil {
		return nil
	}
	return newTextRoundTripFailedError(issues, hasErrors, code, msg)
}

// checkErrorStatus turns an error response into a typed error carrying the
// kernel's code and message, both of which must be strings. Where the response
// also carries a structured payload, one of the lifts above gives the caller a
// type to match on instead of the generic coded error.
func checkErrorStatus(m map[string]any) error {
	status := getString(m, "status")
	if status != "error" {
		return nil
	}
	code, err := requireString(m, "code")
	if err != nil {
		return err
	}
	msg, err := requireString(m, "message")
	if err != nil {
		return err
	}
	if bex := inputBoundExceededFromResponse(code, m); bex != nil {
		return bex
	}
	if vfe := validationFailedFromResponse(code, msg, m); vfe != nil {
		return vfe
	}
	if trte := textRoundtripFailedFromResponse(code, msg, m); trte != nil {
		return trte
	}
	return newCodedError(ErrProtocol, code, msg)
}

// parseSuccessResponse is the answer to a control-plane command that carries
// nothing but its success.
func parseSuccessResponse(raw string) error {
	_, err := decodeResponse(raw, "success")
	return err
}

// parseEventAck reads the answer to an error or remote event. handleTraceEvent
// in Protocol/StreamState.agda resolves both to an acknowledgement, so that is
// the only status either can carry, and the Python and C++ decoders hold their
// events to the same one.
func parseEventAck(raw string) error {
	// Almost every response is one of the two spellings of an acknowledgement,
	// and comparing bytes is cheaper than parsing them.
	if raw == ackCompact || raw == ackSpaced {
		return nil
	}
	_, err := decodeResponse(raw, "ack")
	return err
}

// parseIssueArray decodes the validation issues under a key, for the
// validation response and for the warnings of a parsed DBC. The result is
// empty rather than nil, so encoding it again writes an empty array and not a
// null, which is what the Python decoder answers.
func parseIssueArray(m map[string]any, key string) ([]ValidationIssue, error) {
	issues := []ValidationIssue{}
	for _, item := range getArray(m, key) {
		issue, ok := item.(map[string]any)
		if !ok {
			return nil, protocolError(fmt.Sprintf("expected object in %s array", key))
		}
		var sev IssueSeverity
		switch s := getString(issue, "severity"); s {
		case "error":
			sev = SeverityError
		case "warning":
			sev = SeverityWarning
		default:
			return nil, protocolError(fmt.Sprintf("unknown validation severity: %q", s))
		}
		code := IssueCode(getString(issue, "code"))
		if code == "" {
			code = IssueUnknown
		}
		issues = append(issues, ValidationIssue{
			Severity: sev,
			Code:     code,
			Detail:   getString(issue, "detail"),
		})
	}
	return issues, nil
}

// parseValidationResponse decodes a validateDBC response into typed
// ValidationIssues, preserving severity and the Agda error code.
func parseValidationResponse(raw string) (*ValidationResult, error) {
	m, err := decodeResponse(raw, "validation")
	if err != nil {
		return nil, err
	}
	issues, err := parseIssueArray(m, "issues")
	if err != nil {
		return nil, err
	}
	return &ValidationResult{
		HasErrors: getBool(m, "has_errors"),
		Issues:    issues,
	}, nil
}

// parseExtractionResponse decodes an extractAllSignals JSON response.
// Binary-extraction responses use parseExtractionBin instead.
func parseExtractionResponse(raw string) (*ExtractionResult, error) {
	m, err := decodeResponse(raw, "success")
	if err != nil {
		return nil, err
	}

	var values []SignalValue
	for _, item := range getArray(m, "values") {
		v, ok := item.(map[string]any)
		if !ok {
			return nil, protocolError("expected object in values array")
		}
		r, err := parseRational(v["value"])
		if err != nil {
			return nil, wrapProtocolError("invalid signal value", err)
		}
		name := getString(v, "name")
		if name == "" {
			return nil, protocolError("signal value missing required field: name")
		}
		values = append(values, SignalValue{
			Name:  SignalName(name),
			Value: r,
		})
	}

	var errors []SignalError
	for _, item := range getArray(m, "errors") {
		e, ok := item.(map[string]any)
		if !ok {
			return nil, protocolError("expected object in errors array")
		}
		errors = append(errors, SignalError{
			Name:  SignalName(getString(e, "name")),
			Error: getString(e, "error"),
		})
	}

	var absent []SignalName
	for _, item := range getArray(m, "absent") {
		s, ok := item.(string)
		if !ok {
			return nil, protocolError("expected string in absent array")
		}
		absent = append(absent, SignalName(s))
	}

	result := &ExtractionResult{Values: values, Errors: errors, Absent: absent}
	result.buildIndex()
	return result, nil
}

// parseFrameDataResponse reads a payload out of a JSON response. Only the mock
// backend answers this way; the library returns the bytes themselves.
func parseFrameDataResponse(raw string) (FramePayload, error) {
	m, err := decodeResponse(raw, "success")
	if err != nil {
		return nil, err
	}

	data := getArray(m, "data")
	payload := make(FramePayload, len(data))
	for i, item := range data {
		f, err := parseNumberAsInt64(item)
		if err != nil {
			return nil, wrapProtocolError(fmt.Sprintf("invalid byte %d in frame data", i), err)
		}
		if f < 0 || f > 255 {
			return nil, protocolError(fmt.Sprintf("byte %d out of range: %d", i, f))
		}
		payload[i] = byte(f)
	}
	return payload, nil
}

// parseExtractionBin parses a packed binary extraction buffer into an ExtractionResult.
//
// Buffer layout (canonical wire doc: the processExtractBin header comment in
// src/Aletheia/Main/Binary.agda):
//
//	Header:  [nvals:u16][nerrs:u16][nabss:u16][reasonBytes:u32]  (10 bytes)
//	Values:  nvals × (idx:u16, num:i64, den:i64)                 (18 bytes each)
//	Errors:  nerrs × (idx:u16, code:u8)                          (3 bytes each)
//	Offsets: (nerrs+1) x u32, cumulative byte offsets into Reasons;
//	         off[0] = 0, monotone non-decreasing, off[nerrs] = reasonBytes.
//	Reasons: reasonBytes of UTF-8; error i's reason = bytes [off[i], off[i+1]).
//	Absent:  nabss × (idx:u16)                                   (2 bytes each)
//
// Each reason is the kernel's own string, byte for byte what the JSON path
// carries for the same error. The one-byte code beside it, whose table is
// extractionErrorCodeToℕ in Aletheia.CAN.BatchExtraction, is carried for a
// machine to read but is not put on the result: the JSON path has no such
// field, and the two paths present the same surface. A code outside the table
// is not refused, the reason being what the caller reads.
func parseExtractionBin(buf []byte, names []string) (*ExtractionResult, error) {
	const headerSize = 10
	if len(buf) < headerSize {
		return nil, protocolError("extraction binary buffer too short")
	}
	nvals := int(binary.LittleEndian.Uint16(buf[0:2]))
	nerrs := int(binary.LittleEndian.Uint16(buf[2:4]))
	nabss := int(binary.LittleEndian.Uint16(buf[4:6]))
	reasonBytes := int(binary.LittleEndian.Uint32(buf[6:10]))

	// The size must be exact, short and long alike: either means the writer and
	// this reader disagree about the layout.
	want := headerSize + 18*nvals + 3*nerrs + 4*(nerrs+1) + reasonBytes + 2*nabss
	if len(buf) != want {
		return nil, protocolError(fmt.Sprintf("extraction binary buffer size mismatch: got %d bytes, want %d", len(buf), want))
	}
	off := headerSize

	result := &ExtractionResult{
		Values: make([]SignalValue, 0, nvals),
		Errors: make([]SignalError, 0, nerrs),
		Absent: make([]SignalName, 0, nabss),
	}

	for range nvals {
		idx := binary.LittleEndian.Uint16(buf[off : off+2])
		num := int64(binary.LittleEndian.Uint64(buf[off+2 : off+10]))
		den := int64(binary.LittleEndian.Uint64(buf[off+10 : off+18]))
		off += 18
		name := signalNameByIndex(names, idx)
		// The rational is the kernel's own, never rounded. A denominator of
		// zero or less is a corrupt buffer rather than a value, and the JSON
		// path refuses it too.
		if den <= 0 {
			return nil, protocolError(fmt.Sprintf("non-positive denominator %d for extracted signal %q (index %d)", den, name, idx))
		}
		result.Values = append(result.Values, SignalValue{Name: name, Value: Rational{Numerator: num, Denominator: den}})
	}

	// With no errors and no reasons, which is every frame that extracts
	// cleanly, the three offsets invariants come to the single entry being
	// zero. Anything else, malformed included, takes the general path below.
	if nerrs == 0 && reasonBytes == 0 && binary.LittleEndian.Uint32(buf[off:off+4]) == 0 {
		off += 4
	} else {
		// Each error carries its signal index and its code; the reasons live in
		// the blob at the end, addressed by the offsets table.
		errIdx := make([]uint16, 0, nerrs)
		for range nerrs {
			errIdx = append(errIdx, binary.LittleEndian.Uint16(buf[off:off+2]))
			// The byte after the index is the code, carried but not surfaced.
			off += 3
		}

		// The offsets table is always there, and all three of its invariants
		// hold before anything is sliced out of the blob.
		offsets := make([]int, nerrs+1)
		for i := range offsets {
			offsets[i] = int(binary.LittleEndian.Uint32(buf[off : off+4]))
			off += 4
		}
		if offsets[0] != 0 {
			return nil, protocolError(fmt.Sprintf("extraction binary reason offsets must start at 0, got %d", offsets[0]))
		}
		for i := 1; i < len(offsets); i++ {
			if offsets[i] < offsets[i-1] {
				return nil, protocolError(fmt.Sprintf("extraction binary reason offsets not monotone: offset %d is %d after %d", i, offsets[i], offsets[i-1]))
			}
		}
		if offsets[nerrs] != reasonBytes {
			return nil, protocolError(fmt.Sprintf("extraction binary reason offsets end at %d, want reasonBytes %d", offsets[nerrs], reasonBytes))
		}

		reasons := buf[off : off+reasonBytes]
		off += reasonBytes
		for i, idx := range errIdx {
			reason := reasons[offsets[i]:offsets[i+1]]
			if !utf8.Valid(reason) {
				return nil, protocolError(fmt.Sprintf("extraction binary reason %d is not valid UTF-8", i))
			}
			result.Errors = append(result.Errors, SignalError{Name: signalNameByIndex(names, idx), Error: string(reason)})
		}
	}

	for range nabss {
		idx := binary.LittleEndian.Uint16(buf[off : off+2])
		off += 2
		result.Absent = append(result.Absent, signalNameByIndex(names, idx))
	}

	result.buildIndex()
	return result, nil
}

// signalNameByIndex is the name at an index of the caller's table. An index
// past the table answers a placeholder naming the number, which is for reading
// in a diagnostic: the kernel indexes the table it was given, so reaching it
// means the binding lost track of the names.
func signalNameByIndex(names []string, idx uint16) SignalName {
	if int(idx) < len(names) {
		return SignalName(names[idx])
	}
	return SignalName(fmt.Sprintf("signal_%d", idx))
}

// maxFormulaDepth bounds how deep a formula may nest.
const maxFormulaDepth = 100

// The two spellings of an acknowledgement: the kernel writes the compact one
// and the mock backend the spaced one.
const (
	ackCompact = `{"status":"ack"}`
	ackSpaced  = `{"status": "ack"}`
)

// parseFrameResponse decodes the answer to one frame: an acknowledgement when
// nothing happened, a batch of property events when something did, or a typed
// error. The batch carries every event of the frame, so a mid-stream
// satisfaction reaches the caller beside a violation rather than behind it.
func parseFrameResponse(raw string) (FrameResponse, error) {
	// Fast path: byte-level check before JSON parsing.
	if raw == ackCompact || raw == ackSpaced {
		return Ack{}, nil
	}

	m, err := parseResponse(raw)
	if err != nil {
		return nil, err
	}

	if status := getString(m, "status"); status == "ack" {
		return Ack{}, nil
	} else if status == "error" {
		code := getString(m, "code")
		msg := getString(m, "message")
		if code != "" {
			return nil, newCodedError(ErrProtocol, code, msg)
		}
		return nil, protocolError(msg)
	}

	if respType := getString(m, "type"); respType == "property_batch" {
		rawResults := getArray(m, "results")
		if len(rawResults) == 0 {
			return nil, protocolError("property_batch response 'results' must be non-empty (zero-event frames are encoded as ack)")
		}
		results := make([]PropertyResult, 0, len(rawResults))
		for _, item := range rawResults {
			r, ok := item.(map[string]any)
			if !ok {
				return nil, protocolError("expected object in property_batch results array")
			}
			pr, err := parsePropertyResult(r)
			if err != nil {
				return nil, err
			}
			results = append(results, pr)
		}
		return PropertyBatch{Results: results}, nil
	}

	return nil, protocolError(fmt.Sprintf(
		"unexpected frame response: status=%q, type=%q",
		getString(m, "status"), getString(m, "type"),
	))
}

// parseStreamResponse decodes the end of a stream: one final verdict per
// property.
func parseStreamResponse(raw string) (*StreamResult, error) {
	m, err := decodeResponse(raw, "complete")
	if err != nil {
		return nil, err
	}
	var results []PropertyResult
	for _, item := range getArray(m, "results") {
		r, ok := item.(map[string]any)
		if !ok {
			return nil, protocolError("expected object in results array")
		}
		pr, err := parsePropertyResult(r)
		if err != nil {
			return nil, err
		}
		results = append(results, pr)
	}

	var warnings []StreamWarning
	for _, item := range getArray(m, "warnings") {
		w, ok := item.(map[string]any)
		if !ok {
			return nil, protocolError("expected object in warnings array")
		}
		idx, err := parseNumberAsInt64(w["property_index"])
		if err != nil {
			return nil, wrapProtocolError("warning property_index", err)
		}
		warnings = append(warnings, StreamWarning{
			Kind:          getString(w, "kind"),
			PropertyIndex: int(idx),
			Detail:        getString(w, "detail"),
		})
	}
	return &StreamResult{Results: results, Warnings: warnings}, nil
}

// parsePropertyResult decodes a single endStream verdict object into
// the typed PropertyResult sum (Satisfaction / Violation / Unresolved).
func parsePropertyResult(r map[string]any) (PropertyResult, error) {
	var zero PropertyResult
	entryStatus := getString(r, "status")
	var verdict Verdict
	switch entryStatus {
	case "holds":
		verdict = Holds
	case "fails":
		verdict = Fails
	case "unresolved":
		verdict = Unresolved
	default:
		return zero, protocolError(fmt.Sprintf("unknown verdict status: %q", entryStatus))
	}

	idx, err := parseNumberAsInt64(r["property_index"])
	if err != nil {
		return zero, wrapProtocolError("invalid property_index", err)
	}
	if idx < 0 {
		return zero, protocolError(fmt.Sprintf("negative property_index: %d", idx))
	}

	pr := PropertyResult{
		PropertyIndex: PropertyIndex(idx),
		Verdict:       verdict,
		Reason:        getString(r, "reason"),
	}

	if tsRaw, ok := r["timestamp"]; ok && tsRaw != nil {
		ts, err := parseNumberAsInt64(tsRaw)
		if err != nil {
			return zero, wrapProtocolError("invalid timestamp in result", err)
		}
		if ts < 0 {
			return zero, protocolError(fmt.Sprintf("negative timestamp in result: %d", ts))
		}
		t := Timestamp{Microseconds: ts}
		pr.Timestamp = &t
	}

	return pr, nil
}

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
// [TextRoundTripFailedError]; that and other errors (Agda-side JSON parse
// failure on the input, unexpected status) short-circuit to the (*DBCText,
// error) tuple's error half.
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
		idVal, ext, err := parseCanIDFields(rvdRaw)
		if err != nil {
			return DBCRawValueDesc{}, wrapProtocolError("invalid unresolvedValueDesc id", err)
		}
		var canID CANID
		if ext {
			eid, err := NewExtendedID(idVal)
			if err != nil {
				return DBCRawValueDesc{}, err
			}
			canID = eid
		} else {
			sid, err := NewStandardID(uint16(idVal))
			if err != nil {
				return DBCRawValueDesc{}, err
			}
			canID = sid
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
			SignalName: getString(rvdRaw, "signalName"),
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
		return DBCNode{Name: getString(nRaw, "name")}, nil
	})
}

// parseCanIDFields reads the identifier pair every message-scoped or
// signal-scoped target carries. An absent extended flag means a standard
// identifier.
func parseCanIDFields(m map[string]any) (uint32, bool, error) {
	idVal, err := parseNumberAsInt64(m["id"])
	if err != nil {
		return 0, false, wrapProtocolError("invalid id", err)
	}
	if idVal < 0 || idVal > math.MaxUint32 {
		return 0, false, protocolError(fmt.Sprintf("id out of uint32 range: %d", idVal))
	}
	return uint32(idVal), getBool(m, "extended"), nil
}

// parseCommentTarget decodes what a comment is attached to, refusing a kind
// the format does not have, as the kernel's own parser does.
func parseCommentTarget(m map[string]any) (DBCCommentTarget, error) {
	kind := getString(m, "kind")
	switch kind {
	case "network":
		return DBCCommentTargetNetwork{}, nil
	case "node":
		return DBCCommentTargetNode{Node: getString(m, "node")}, nil
	case "message":
		id, ext, err := parseCanIDFields(m)
		if err != nil {
			return nil, err
		}
		return DBCCommentTargetMessage{ID: id, Extended: ext}, nil
	case "signal":
		id, ext, err := parseCanIDFields(m)
		if err != nil {
			return nil, err
		}
		return DBCCommentTargetSignal{ID: id, Extended: ext, Signal: getString(m, "signal")}, nil
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
		return DBCAttrTargetNode{Node: getString(m, "node")}, nil
	case "message":
		id, ext, err := parseCanIDFields(m)
		if err != nil {
			return nil, err
		}
		return DBCAttrTargetMessage{ID: id, Extended: ext}, nil
	case "signal":
		id, ext, err := parseCanIDFields(m)
		if err != nil {
			return nil, err
		}
		return DBCAttrTargetSignal{ID: id, Extended: ext, Signal: getString(m, "signal")}, nil
	case "envVar":
		return DBCAttrTargetEnvVar{EnvVar: getString(m, "envVar")}, nil
	case "nodeMsg":
		id, ext, err := parseCanIDFields(m)
		if err != nil {
			return nil, err
		}
		return DBCAttrTargetNodeMsg{Node: getString(m, "node"), ID: id, Extended: ext}, nil
	case "nodeSig":
		id, ext, err := parseCanIDFields(m)
		if err != nil {
			return nil, err
		}
		return DBCAttrTargetNodeSig{
			Node:     getString(m, "node"),
			ID:       id,
			Extended: ext,
			Signal:   getString(m, "signal"),
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
	if idVal < 0 {
		return nil, protocolError(fmt.Sprintf("negative message id: %d", idVal))
	}
	extended := false
	if v, ok := j["extended"]; ok {
		b, isBool := v.(bool)
		if !isBool {
			return nil, protocolError("message \"extended\" must be a boolean")
		}
		extended = b
	}

	var id CANID
	if extended {
		if idVal > math.MaxUint32 {
			return nil, protocolError(fmt.Sprintf("CAN ID %d exceeds uint32 range", idVal))
		}
		eid, err := NewExtendedID(uint32(idVal))
		if err != nil {
			return nil, err
		}
		id = eid
	} else {
		sid, err := NewStandardID(uint16(idVal))
		if err != nil {
			return nil, err
		}
		id = sid
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

	var senders []string
	if raw, ok := j["senders"].([]any); ok {
		senders = make([]string, 0, len(raw))
		for _, s := range raw {
			ss, sOk := s.(string)
			if !sOk {
				return nil, protocolError("senders entry is not a string")
			}
			senders = append(senders, ss)
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

	var receivers []string
	if raw, ok := j["receivers"].([]any); ok {
		receivers = make([]string, 0, len(raw))
		for _, r := range raw {
			rs, rOk := r.(string)
			if !rOk {
				return zero, protocolError("receivers entry is not a string")
			}
			receivers = append(receivers, rs)
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
		rawVals, ok := j["multiplex_values"].([]any)
		if !ok || len(rawVals) == 0 {
			return nil, protocolError("multiplexed signal requires a non-empty \"multiplex_values\" array")
		}
		muxVals := make([]MultiplexValue, 0, len(rawVals))
		for i, rv := range rawVals {
			v, err := parseNumberAsInt64(rv)
			if err != nil {
				return nil, wrapProtocolError(fmt.Sprintf("invalid multiplex_values[%d]", i), err)
			}
			if v < 0 || v > math.MaxUint32 {
				return nil, protocolError(fmt.Sprintf("multiplex_values[%d] %d out of range (0-%d)", i, v, uint32(math.MaxUint32)))
			}
			muxVals = append(muxVals, MultiplexValue(v))
		}
		return Multiplexed{
			Multiplexor:     SignalName(muxName),
			MultiplexValues: muxVals,
		}, nil
	default:
		return nil, protocolError(fmt.Sprintf("unknown signal presence %q", presence))
	}
}
