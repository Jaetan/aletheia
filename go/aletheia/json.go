package aletheia

import (
	"encoding/binary"
	"encoding/json"
	"fmt"
	"math"
	"math/big"
	"strconv"
	"strings"
)

// bytesToIntSlice converts []byte to []int for JSON serialization.
// Go's json.Marshal encodes []byte/[]uint8 as base64, but the Agda core
// expects a JSON array of integers: [0, 64, 31, ...].
func bytesToIntSlice(data []byte) []int {
	out := make([]int, len(data))
	for i, b := range data {
		out[i] = int(b)
	}
	return out
}

// --- Serialization (Go → JSON for Agda core) ---

// serializeCommand builds the JSON envelope sent to the Agda core for
// control-plane commands (parseDBC, setProperties, validateDBC, …).
// Go's encoding/json marshals map keys in lexical order, so the wire
// output is deterministic across runs.
func serializeCommand(command string, fields map[string]any) (string, error) {
	m := map[string]any{"type": "command", "command": command}
	for k, v := range fields {
		m[k] = v
	}
	b, err := json.Marshal(m)
	if err != nil {
		return "", wrapProtocolError("failed to serialize command", err)
	}
	return string(b), nil
}

// serializeDataFrame serializes a CAN frame as a JSON data event.
// Uses direct string building rather than json.Marshal to avoid map allocation
// and reflection overhead.
//
// R19 cluster 19 / GO-B-25.2 DEFER (2026-05-12): the per-call
// `strings.Builder` allocation here was flagged as a `sync.Pool` candidate.
// Audit (`grep -rn 'serializeDataFrame'`) confirmed the function is only
// invoked from `mock.go:135` (the test backend) and `check_test.go` —
// real streaming uses the binary FFI `sendFrameBinary` and never enters
// this path.  A pool would add `Get`/`Put` overhead on test paths where
// the existing single-allocation cost is already negligible, in exchange
// for zero real-world benefit.  Re-evaluate only if a JSON streaming
// surface is added that calls this function on a hot path.
//
// R20 cluster F (GO-B-14.1 / GO-D-16.2): BRS/ESI trailing args are
// emitted as optional `"brs"`/`"esi"` fields when non-nil so
// mock-driven tests can assert on the wire shape end-to-end.  Pass
// `nil, nil` for CAN 2.0B frames where these bits don't exist (ISO
// 11898-1:2015 §10.4.2/3 — CAN-FD only).  The Agda data-event parser
// ignores unknown fields, so this is purely an additive wire-shape
// observability for cross-binding-test parity.
func serializeDataFrame(ts Timestamp, id CANID, dlc DLC, data FramePayload, brs, esi *bool) string {
	// Avoids map allocation, reflection-based marshaling, and []int conversion.
	var buf strings.Builder
	buf.Grow(128 + len(data)*4) // pre-size for typical frame
	buf.WriteString(`{"type":"data","timestamp":`)
	buf.WriteString(strconv.FormatInt(ts.Microseconds, 10))
	buf.WriteString(`,"id":`)
	buf.WriteString(strconv.FormatUint(uint64(id.Value()), 10))
	buf.WriteString(`,"extended":`)
	if id.IsExtended() {
		buf.WriteString("true")
	} else {
		buf.WriteString("false")
	}
	buf.WriteString(`,"dlc":`)
	buf.WriteString(strconv.FormatUint(uint64(dlc.Value()), 10))
	buf.WriteString(`,"data":[`)
	for i, b := range data {
		if i > 0 {
			buf.WriteByte(',')
		}
		buf.WriteString(strconv.FormatUint(uint64(b), 10))
	}
	buf.WriteByte(']')
	if brs != nil {
		buf.WriteString(`,"brs":`)
		if *brs {
			buf.WriteString("true")
		} else {
			buf.WriteString("false")
		}
	}
	if esi != nil {
		buf.WriteString(`,"esi":`)
		if *esi {
			buf.WriteString("true")
		} else {
			buf.WriteString("false")
		}
	}
	buf.WriteByte('}')
	return buf.String()
}

// serializeErrorEvent serializes a CAN error event as JSON. Used by the
// MockBackend so tests can observe error events alongside data frames.
func serializeErrorEvent(ts Timestamp) string {
	var buf strings.Builder
	buf.Grow(48)
	buf.WriteString(`{"type":"error","timestamp":`)
	buf.WriteString(strconv.FormatInt(ts.Microseconds, 10))
	buf.WriteByte('}')
	return buf.String()
}

// serializeRemoteEvent serializes a CAN remote frame event as JSON. Used by the
// MockBackend so tests can observe remote events alongside data frames.
func serializeRemoteEvent(ts Timestamp, id CANID) string {
	var buf strings.Builder
	buf.Grow(80)
	buf.WriteString(`{"type":"remote","timestamp":`)
	buf.WriteString(strconv.FormatInt(ts.Microseconds, 10))
	buf.WriteString(`,"id":`)
	buf.WriteString(strconv.FormatUint(uint64(id.Value()), 10))
	buf.WriteString(`,"extended":`)
	if id.IsExtended() {
		buf.WriteString("true")
	} else {
		buf.WriteString("false")
	}
	buf.WriteByte('}')
	return buf.String()
}

// serializeDBC converts a DBCDefinition into the map shape Agda expects
// under the "dbc" field of the parseDBC / validateDBC command envelopes.
//
// Defense-in-depth (R19 cluster E1, R19-CARRY-3 / GO-B-28.4 closure): a
// `MaxDBCTextBytes` size cap is applied to the marshaled envelope before
// it leaves Go.  In normal flow the upstream parser bound (per UR-2)
// makes this redundant; the guard catches any internal blowup or future
// bypass that lets an oversized in-memory `DBCDefinition` reach the
// serializer.
func serializeDBC(dbc DBCDefinition) (map[string]any, error) {
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
			switch sig.ByteOrder {
			case BigEndian:
				s["byteOrder"] = "big_endian"
			case LittleEndian:
				s["byteOrder"] = "little_endian"
			default:
				return nil, validationError(fmt.Sprintf("invalid byte order %d", sig.ByteOrder))
			}
			// R19 cluster 17 / PY-D-19.2: emit explicit "presence"
			// discriminator on multiplexed signals (mirrors Always
			// signals' "presence": "always").  Cross-binding parity
			// with the Agda Formatter and the Python TypedDict.
			if mux, ok := sig.Presence.(Multiplexed); ok {
				s["presence"] = "multiplexed"
				s["multiplexor"] = string(mux.Multiplexor)
				vals := make([]uint32, len(mux.MuxValues))
				for i, v := range mux.MuxValues {
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
		// Mirror the Agda wire form: emit "extended" only when the CAN ID is
		// extended (29-bit). Agda omits the field for standard 11-bit frames;
		// its parser accepts both forms but the omit-when-false shape is
		// canonical (matches attachCANID used for comment / attribute targets,
		// and the same convention enforced by the Python and C++ bindings — B.3.j).
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

	// Track E.8 (Plan B): unresolved RawValueDescs from the text-parse path.
	// Wire shape mirrors message_to_json's leading {id, extended} pair via
	// attachCANID; the rest is signalName + entries (parallel to value tables).
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
	// Defense-in-depth bound check (see function-level comment).
	probe, err := json.Marshal(out)
	if err != nil {
		return nil, wrapProtocolError("failed to size-check DBC", err)
	}
	if size := uint64(len(probe)); size > MaxDBCTextBytes {
		return nil, &InputBoundExceededError{
			BoundKind: BoundKindInputLengthBytes,
			Observed:  size,
			Limit:     MaxDBCTextBytes,
		}
	}
	return out, nil
}

// --- Tier 2 serializers (Go → JSON for Agda core) ---

// attachCANID mirrors the Agda formatter: emits "id" unconditionally and
// "extended" only when true. Matching formatCANId keeps 11-bit frames
// byte-identical to Tier 1 wire output.
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

// validateRational rejects rationals the wire format cannot represent
// (zero or negative denominator).  Predicate values carry exact
// [Rational] per the DecRat universal principle (cluster 17 / GO-D-19.1
// mirror of PY-D-19.1); the NaN / ±Inf rejection that the float64 path
// needed (R19 cluster 7 — GO-B-8.1) is structurally absent — Rational
// has no NaN / Inf representation — but denominator validation remains.
func validateRational(name string, r Rational) error {
	if r.Denominator <= 0 {
		return validationError(fmt.Sprintf("%s: non-positive denominator %d (must be > 0)",
			name, r.Denominator))
	}
	return nil
}

// rationalLess reports r1 < r2 by comparing cross-products with the
// (positive) denominators (validateRational is the precondition).
//
// Cross-product overflow is avoided by widening to math/big.Int — naive
// int64 multiplication wraps silently (e.g. {MaxInt64, 2} vs {1, 2}
// would falsely report r1 < r2 with int64 wraparound).
func rationalLess(r1, r2 Rational) bool {
	a := new(big.Int).Mul(big.NewInt(r1.Numerator), big.NewInt(r2.Denominator))
	b := new(big.Int).Mul(big.NewInt(r2.Numerator), big.NewInt(r1.Denominator))
	return a.Cmp(b) < 0
}

// serializePredicate encodes a Predicate into the JSON tag/field shape
// consumed by the Agda LTL parser (SignalPredicate.JSON).
func serializePredicate(p Predicate) (map[string]any, error) {
	switch p := p.(type) {
	case Equals:
		if err := validateRational("equals.value", p.Value); err != nil {
			return nil, err
		}
		return map[string]any{"predicate": "equals", "signal": string(p.Signal), "value": serializeRational(p.Value)}, nil
	case LessThan:
		if err := validateRational("lessThan.value", p.Value); err != nil {
			return nil, err
		}
		return map[string]any{"predicate": "lessThan", "signal": string(p.Signal), "value": serializeRational(p.Value)}, nil
	case GreaterThan:
		if err := validateRational("greaterThan.value", p.Value); err != nil {
			return nil, err
		}
		return map[string]any{"predicate": "greaterThan", "signal": string(p.Signal), "value": serializeRational(p.Value)}, nil
	case LessThanOrEqual:
		if err := validateRational("lessThanOrEqual.value", p.Value); err != nil {
			return nil, err
		}
		return map[string]any{"predicate": "lessThanOrEqual", "signal": string(p.Signal), "value": serializeRational(p.Value)}, nil
	case GreaterThanOrEqual:
		if err := validateRational("greaterThanOrEqual.value", p.Value); err != nil {
			return nil, err
		}
		return map[string]any{"predicate": "greaterThanOrEqual", "signal": string(p.Signal), "value": serializeRational(p.Value)}, nil
	case Between:
		if err := validateRational("between.min", p.Min); err != nil {
			return nil, err
		}
		if err := validateRational("between.max", p.Max); err != nil {
			return nil, err
		}
		if rationalLess(p.Max, p.Min) {
			return nil, validationError(fmt.Sprintf("between: min (%g) exceeds max (%g)",
				p.Min.Float64(), p.Max.Float64()))
		}
		return map[string]any{"predicate": "between", "signal": string(p.Signal), "min": serializeRational(p.Min), "max": serializeRational(p.Max)}, nil
	case ChangedBy:
		if err := validateRational("changedBy.delta", p.Delta); err != nil {
			return nil, err
		}
		return map[string]any{"predicate": "changedBy", "signal": string(p.Signal), "delta": serializeRational(p.Delta)}, nil
	case StableWithin:
		if err := validateRational("stableWithin.tolerance", p.Tolerance); err != nil {
			return nil, err
		}
		if p.Tolerance.Numerator < 0 {
			return nil, validationError(fmt.Sprintf("negative tolerance: %g", p.Tolerance.Float64()))
		}
		return map[string]any{"predicate": "stableWithin", "signal": string(p.Signal), "tolerance": serializeRational(p.Tolerance)}, nil
	default:
		return nil, validationError(fmt.Sprintf("unsupported predicate type %T", p))
	}
}

// validateTimeBound rejects TimeBounds the Agda core cannot represent
// (negative microseconds or overflow past int64 in the wire payload).
func validateTimeBound(t TimeBound) error {
	if t.Microseconds < 0 {
		return validationError(fmt.Sprintf("negative time bound: %d microseconds", t.Microseconds))
	}
	return nil
}

// serializeFormula encodes an LTL formula AST for Agda, bounded in depth
// to prevent unbounded recursion on pathological user input.
func serializeFormula(f Formula) (map[string]any, error) {
	return serializeFormulaDepth(f, 0)
}

// serializeFormulaDepth is the recursive core of serializeFormula. It
// carries the remaining depth budget so deeply nested user input fails
// fast instead of blowing the Go stack.
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
		inner, err := serializeFormulaDepth(f.Inner, depth+1)
		if err != nil {
			return nil, err
		}
		return map[string]any{"operator": "not", "formula": inner}, nil
	case And:
		left, err := serializeFormulaDepth(f.Left, depth+1)
		if err != nil {
			return nil, err
		}
		right, err := serializeFormulaDepth(f.Right, depth+1)
		if err != nil {
			return nil, err
		}
		return map[string]any{"operator": "and", "left": left, "right": right}, nil
	case Or:
		left, err := serializeFormulaDepth(f.Left, depth+1)
		if err != nil {
			return nil, err
		}
		right, err := serializeFormulaDepth(f.Right, depth+1)
		if err != nil {
			return nil, err
		}
		return map[string]any{"operator": "or", "left": left, "right": right}, nil
	case Next:
		inner, err := serializeFormulaDepth(f.Inner, depth+1)
		if err != nil {
			return nil, err
		}
		return map[string]any{"operator": "next", "formula": inner}, nil
	case WeakNext:
		inner, err := serializeFormulaDepth(f.Inner, depth+1)
		if err != nil {
			return nil, err
		}
		return map[string]any{"operator": "weakNext", "formula": inner}, nil
	case Always:
		inner, err := serializeFormulaDepth(f.Inner, depth+1)
		if err != nil {
			return nil, err
		}
		return map[string]any{"operator": "always", "formula": inner}, nil
	case Eventually:
		inner, err := serializeFormulaDepth(f.Inner, depth+1)
		if err != nil {
			return nil, err
		}
		return map[string]any{"operator": "eventually", "formula": inner}, nil
	case Until:
		left, err := serializeFormulaDepth(f.Left, depth+1)
		if err != nil {
			return nil, err
		}
		right, err := serializeFormulaDepth(f.Right, depth+1)
		if err != nil {
			return nil, err
		}
		return map[string]any{"operator": "until", "left": left, "right": right}, nil
	case Release:
		left, err := serializeFormulaDepth(f.Left, depth+1)
		if err != nil {
			return nil, err
		}
		right, err := serializeFormulaDepth(f.Right, depth+1)
		if err != nil {
			return nil, err
		}
		return map[string]any{"operator": "release", "left": left, "right": right}, nil
	case MetricAlways:
		if err := validateTimeBound(f.Bound); err != nil {
			return nil, err
		}
		inner, err := serializeFormulaDepth(f.Inner, depth+1)
		if err != nil {
			return nil, err
		}
		return map[string]any{"operator": "metricAlways", "timebound": f.Bound.Microseconds, "formula": inner}, nil
	case MetricEventually:
		if err := validateTimeBound(f.Bound); err != nil {
			return nil, err
		}
		inner, err := serializeFormulaDepth(f.Inner, depth+1)
		if err != nil {
			return nil, err
		}
		return map[string]any{"operator": "metricEventually", "timebound": f.Bound.Microseconds, "formula": inner}, nil
	case MetricUntil:
		if err := validateTimeBound(f.Bound); err != nil {
			return nil, err
		}
		left, err := serializeFormulaDepth(f.Left, depth+1)
		if err != nil {
			return nil, err
		}
		right, err := serializeFormulaDepth(f.Right, depth+1)
		if err != nil {
			return nil, err
		}
		return map[string]any{"operator": "metricUntil", "timebound": f.Bound.Microseconds, "left": left, "right": right}, nil
	case MetricRelease:
		if err := validateTimeBound(f.Bound); err != nil {
			return nil, err
		}
		left, err := serializeFormulaDepth(f.Left, depth+1)
		if err != nil {
			return nil, err
		}
		right, err := serializeFormulaDepth(f.Right, depth+1)
		if err != nil {
			return nil, err
		}
		return map[string]any{"operator": "metricRelease", "timebound": f.Bound.Microseconds, "left": left, "right": right}, nil
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
	case float64:
		// Agda sends integers as float64 in JSON.
		if math.Trunc(n) != n {
			return Rational{}, protocolError(fmt.Sprintf("expected integer rational, got fractional float64: %v", n))
		}
		if n > math.MaxInt64 || n < math.MinInt64 {
			return Rational{}, protocolError(fmt.Sprintf("rational out of int64 range: %v", n))
		}
		return Rational{Numerator: int64(n), Denominator: 1}, nil
	case map[string]any:
		num, ok1 := n["numerator"].(float64)
		den, ok2 := n["denominator"].(float64)
		if !ok1 || !ok2 {
			return Rational{}, protocolError(fmt.Sprintf("rational dict missing fields: %v", v))
		}
		// Reject non-integer components before any int64 cast: `int64(0.5)`
		// silently truncates to 0, which would mis-classify a fractional
		// denominator as "zero denominator" and a fractional numerator as
		// a silent precision loss.  R20 cluster H — GO-B-12.1.
		if num != math.Trunc(num) || den != math.Trunc(den) {
			return Rational{}, protocolError(fmt.Sprintf("expected integer rational, got %v/%v", num, den))
		}
		if num > math.MaxInt64 || num < math.MinInt64 || den > math.MaxInt64 || den < math.MinInt64 {
			return Rational{}, protocolError(fmt.Sprintf("rational components out of int64 range: %v/%v", num, den))
		}
		if den == 0 {
			return Rational{}, protocolError(fmt.Sprintf("zero denominator in rational: %v", v))
		}
		// Reject negative denominators rather than rewriting them.
		// Python and the Agda core reject `den < 0` at parse time;
		// silently rewriting here would let asymmetric wire shapes
		// pass through Go-only paths and surface as parity failures
		// (per `feedback_cross_binding_wire_symmetry.md`).  R19
		// cluster 7 — GO-B-8.2.
		if den < 0 {
			return Rational{}, protocolError(fmt.Sprintf("negative denominator in rational: %v", v))
		}
		return Rational{Numerator: int64(num), Denominator: int64(den)}, nil
	default:
		return Rational{}, protocolError(fmt.Sprintf("expected number or rational dict, got %T", v))
	}
}

// serializeRational emits a Rational as {"numerator","denominator"} so
// the wire form preserves exact precision (no float rounding).
func serializeRational(r Rational) any {
	if r.Denominator == 1 {
		return r.Numerator
	}
	return map[string]any{"numerator": r.Numerator, "denominator": r.Denominator}
}

// --- Deserialization (JSON from Agda core → Go) ---

// parseNumber handles the three number formats Agda emits:
// plain int, plain float, or {"numerator": n, "denominator": d}.
func parseNumber(v any) (float64, error) {
	switch n := v.(type) {
	case float64:
		return n, nil
	case map[string]any:
		// Agda emits rationals as {"numerator": n, "denominator": d} with plain numbers.
		numF, ok1 := n["numerator"].(float64)
		denF, ok2 := n["denominator"].(float64)
		if !ok1 || !ok2 {
			return 0, protocolError(fmt.Sprintf("expected {numerator: number, denominator: number}, got %v", n))
		}
		if denF == 0 {
			return 0, protocolError("zero denominator in rational")
		}
		return numF / denF, nil
	default:
		return 0, protocolError(fmt.Sprintf("expected number, got %T: %v", v, v))
	}
}

// parseNumberAsInt64 parses a JSON number as an exact integer.
// Note: Go's json.Unmarshal decodes all numbers as float64 (53-bit mantissa),
// so integers above 2^53 lose precision silently. This is acceptable for CAN
// fields (IDs ≤ 29 bits, timestamps ≪ 2^53).
func parseNumberAsInt64(v any) (int64, error) {
	switch n := v.(type) {
	case float64:
		if n != math.Trunc(n) {
			return 0, protocolError(fmt.Sprintf("expected integer, got fractional: %v", n))
		}
		if n > math.MaxInt64 || n < math.MinInt64 {
			return 0, protocolError(fmt.Sprintf("integer out of int64 range: %v", n))
		}
		return int64(n), nil
	case map[string]any:
		// Agda emits rationals as {"numerator": n, "denominator": d} with plain numbers.
		numF, ok1 := n["numerator"].(float64)
		denF, ok2 := n["denominator"].(float64)
		if !ok1 || !ok2 {
			return 0, protocolError(fmt.Sprintf("expected {numerator: number, denominator: number}, got %v", n))
		}
		if numF != math.Trunc(numF) || denF != math.Trunc(denF) {
			return 0, protocolError(fmt.Sprintf("expected integer rational, got %v/%v", numF, denF))
		}
		numI, denI := int64(numF), int64(denF)
		if denI == 0 {
			return 0, protocolError("zero denominator in rational")
		}
		if numI%denI != 0 {
			return 0, protocolError(fmt.Sprintf("expected integer, got non-exact rational %d/%d", numI, denI))
		}
		return numI / denI, nil
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

// parseResponse unmarshals an Agda core response into a generic map
// before typed parsers narrow it to a concrete response variant.
func parseResponse(raw string) (map[string]any, error) {
	var m map[string]any
	if err := json.Unmarshal([]byte(raw), &m); err != nil {
		return nil, wrapProtocolError("invalid JSON response", err)
	}
	return m, nil
}

// requireString extracts a string field from a parsed JSON object, returning
// a protocol error if the field is missing or not a string. Used by error-
// response parsing where the Agda core guarantees both fields are present;
// a silent default would paper over FFI drift or a malformed stub (see
// aletheia-py's “build_error_response“ for the canonical rationale).
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

// inputBoundExceededFromResponse lifts a wire response carrying
// “bound_kind“ / “observed“ / “limit“ into a typed
// [InputBoundExceededError].  Returns nil when any of the three fields
// is missing or ill-typed (matches C++ “make_json_error“'s
// degrade-to-nullopt rule and Python “build_error_response“'s
// triple-must-be-complete check).  The wire “message“ string is not
// threaded through — “*InputBoundExceededError.Error()“ reconstructs an
// equivalent string from kind/observed/limit, matching cross-binding
// convention where each language formats the message in its own idiom.
// AGDA-D-13.4 phase 2a — cross-binding wire-symmetric lifting; previously
// only the binding-side short-circuit raised this type, so kernel-rejected
// paths (NestingDepth, AtomCount) returned a generic *Error.
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

// jsonNumberToUint64 narrows a JSON-decoded numeric value to uint64.
// Rejects negatives, non-integers, and overflowing magnitudes.
func jsonNumberToUint64(v any) (uint64, bool) {
	switch n := v.(type) {
	case float64:
		if n < 0 || n > float64(^uint64(0)) || n != float64(uint64(n)) {
			return 0, false
		}
		return uint64(n), true
	case int:
		if n < 0 {
			return 0, false
		}
		return uint64(n), true
	case int64:
		if n < 0 {
			return 0, false
		}
		return uint64(n), true
	case uint64:
		return n, true
	default:
		return 0, false
	}
}

// checkErrorStatus converts a parsed response with status="error" into
// a typed error carrying the Agda-side code and message. Both “code“
// and “message“ must be non-null strings — a missing or non-string
// value surfaces as a protocol error rather than being papered over with
// a default, matching Python's “build_error_response“ strict contract.
//
// InputBoundExceeded responses lift the structured triple into a typed
// [InputBoundExceededError] when all three of “bound_kind“ /
// “observed“ / “limit“ are present; mirrors Python's
// “build_error_response“ and C++'s “make_json_error“ lifting.
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
	return newCodedError(ErrProtocol, code, msg)
}

// parseSuccessResponse validates an Agda command response for control-
// plane commands (parseDBC, setProperties, …) and returns nil iff
// status=="success".
func parseSuccessResponse(raw string) error {
	m, err := parseResponse(raw)
	if err != nil {
		return err
	}
	if err := checkErrorStatus(m); err != nil {
		return err
	}
	status := getString(m, "status")
	if status == "success" {
		return nil
	}
	return protocolError(fmt.Sprintf("unexpected status: %q", status))
}

// parseEventAck parses a send_error / send_remote response. Trace events
// (Error / Remote) always resolve to Response.Ack in the Agda core — see
// Protocol/StreamState.agda handleTraceEvent — so the wire status is "ack".
// Python parse_event_response and C++ parse_event_ack enforce the same.
func parseEventAck(raw string) error {
	// Fast path: byte-level check before JSON parsing (~99% of real traffic).
	if raw == ackCompact || raw == ackSpaced {
		return nil
	}
	m, err := parseResponse(raw)
	if err != nil {
		return err
	}
	if err := checkErrorStatus(m); err != nil {
		return err
	}
	status := getString(m, "status")
	if status == "ack" {
		return nil
	}
	return protocolError(fmt.Sprintf("unexpected status: %q", status))
}

// parseValidationResponse decodes a validateDBC response into typed
// ValidationIssues, preserving severity and the Agda error code.
func parseValidationResponse(raw string) (*ValidationResult, error) {
	m, err := parseResponse(raw)
	if err != nil {
		return nil, err
	}
	if err := checkErrorStatus(m); err != nil {
		return nil, err
	}
	status := getString(m, "status")
	if status != "validation" {
		return nil, protocolError(fmt.Sprintf("expected validation response, got status: %q", status))
	}

	// Initialize empty (not nil) so JSON marshaling produces "[]" instead
	// of "null"; matches Python's empty-list default per
	// feedback_cross_language_parity.md (R18 cluster 5 cross-binding test
	// caught the nil-vs-empty drift).
	issues := []ValidationIssue{}
	for _, item := range getArray(m, "issues") {
		issue, ok := item.(map[string]any)
		if !ok {
			return nil, protocolError("expected object in issues array")
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
	return &ValidationResult{
		HasErrors: getBool(m, "has_errors"),
		Issues:    issues,
	}, nil
}

// parseExtractionResponse decodes an extractAllSignals JSON response.
// Binary-extraction responses use parseExtractionBin instead.
func parseExtractionResponse(raw string) (*ExtractionResult, error) {
	m, err := parseResponse(raw)
	if err != nil {
		return nil, err
	}
	if err := checkErrorStatus(m); err != nil {
		return nil, err
	}
	status := getString(m, "status")
	if status != "success" {
		return nil, protocolError(fmt.Sprintf("expected success response, got status: %q", status))
	}

	var values []SignalValue
	for _, item := range getArray(m, "values") {
		v, ok := item.(map[string]any)
		if !ok {
			return nil, protocolError("expected object in values array")
		}
		val, err := parseNumber(v["value"])
		if err != nil {
			return nil, wrapProtocolError("invalid signal value", err)
		}
		name := getString(v, "name")
		if name == "" {
			return nil, protocolError("signal value missing required field: name")
		}
		values = append(values, SignalValue{
			Name:  SignalName(name),
			Value: PhysicalValue(val),
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

// parseFrameDataResponse decodes a {"status":"success","data":[...]} response
// into the raw CAN payload bytes. Used only by MockBackend — the real FFI path
// returns raw bytes directly via aletheia_build_frame_bin / aletheia_update_frame_bin.
func parseFrameDataResponse(raw string) (FramePayload, error) {
	m, err := parseResponse(raw)
	if err != nil {
		return nil, err
	}
	if err := checkErrorStatus(m); err != nil {
		return nil, err
	}
	status := getString(m, "status")
	if status != "success" {
		return nil, protocolError(fmt.Sprintf("expected success response, got status: %q", status))
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

// extractionErrorMessages maps error codes from binary extraction to messages.
// Must match Agda categorizeIndexed: 0 = not_in_dbc, 1 = out_of_bounds, 2 = extraction_failed.
var extractionErrorMessages = [...]string{
	"Signal not found in DBC",
	"Value out of bounds",
	"Extraction failed",
}

// parseExtractionBin parses a packed binary extraction buffer into an ExtractionResult.
// Buffer layout: [nvals:u16][nerrs:u16][nabss:u16] + values(18B) + errors(3B) + absent(2B).
func parseExtractionBin(buf []byte, names []string) (*ExtractionResult, error) {
	if len(buf) < 6 {
		return nil, protocolError("extraction binary buffer too short")
	}
	nvals := binary.LittleEndian.Uint16(buf[0:2])
	nerrs := binary.LittleEndian.Uint16(buf[2:4])
	nabss := binary.LittleEndian.Uint16(buf[4:6])
	off := 6

	result := &ExtractionResult{
		Values: make([]SignalValue, 0, nvals),
		Errors: make([]SignalError, 0, nerrs),
		Absent: make([]SignalName, 0, nabss),
	}

	for range nvals {
		if off+18 > len(buf) {
			return nil, protocolError("extraction binary buffer truncated in values")
		}
		idx := binary.LittleEndian.Uint16(buf[off : off+2])
		num := int64(binary.LittleEndian.Uint64(buf[off+2 : off+10]))
		den := int64(binary.LittleEndian.Uint64(buf[off+10 : off+18]))
		off += 18
		name := signalNameByIndex(names, idx)
		var value float64
		if den != 0 {
			value = float64(num) / float64(den)
		}
		result.Values = append(result.Values, SignalValue{Name: name, Value: PhysicalValue(value)})
	}

	for range nerrs {
		if off+3 > len(buf) {
			return nil, protocolError("extraction binary buffer truncated in errors")
		}
		idx := binary.LittleEndian.Uint16(buf[off : off+2])
		code := buf[off+2]
		off += 3
		name := signalNameByIndex(names, idx)
		var msg string
		if int(code) < len(extractionErrorMessages) {
			msg = extractionErrorMessages[code]
		} else {
			msg = fmt.Sprintf("unknown error code %d", code)
		}
		result.Errors = append(result.Errors, SignalError{Name: name, Error: msg})
	}

	for range nabss {
		if off+2 > len(buf) {
			return nil, protocolError("extraction binary buffer truncated in absent")
		}
		idx := binary.LittleEndian.Uint16(buf[off : off+2])
		off += 2
		result.Absent = append(result.Absent, signalNameByIndex(names, idx))
	}

	// Reject trailing bytes: the header (6B) + all entries must consume the whole
	// buffer. Extra bytes indicate a protocol mismatch between Agda writer and Go
	// reader and would silently hide bugs if ignored.
	if off != len(buf) {
		return nil, protocolError(fmt.Sprintf("extraction binary buffer has %d trailing bytes", len(buf)-off))
	}

	result.buildIndex()
	return result, nil
}

// signalNameByIndex resolves a DBC signal index into its name using the
// caller-supplied lookup table. Returns an empty SignalName on OOB.
func signalNameByIndex(names []string, idx uint16) SignalName {
	if int(idx) < len(names) {
		return SignalName(names[idx])
	}
	return SignalName(fmt.Sprintf("signal_%d", idx))
}

// maxFormulaDepth bounds recursion in the parsed-formula tree (parseFormulaJSON).
// Unrelated to the streaming hot path; defined here because both this and the
// ack-fast-path constants live in json.go's parse-side helpers.
const maxFormulaDepth = 100

// Ack fast path constants — avoid json.Unmarshal for ~99% of streaming frames.
// The Agda core emits exactly {"status":"ack"} (compact). The spaced variant
// covers json.Marshal output used by MockBackend.
const (
	ackCompact = `{"status":"ack"}`
	ackSpaced  = `{"status": "ack"}`
)

// parseFrameResponse decodes the per-frame LTL verdict returned by
// sendFrame: Ack (no violation) or Violation (with property index).
func parseFrameResponse(raw string) (FrameResponse, error) {
	// Fast path: byte-level check before JSON parsing.
	if raw == ackCompact || raw == ackSpaced {
		return Ack{}, nil
	}

	m, err := parseResponse(raw)
	if err != nil {
		return nil, err
	}

	status := getString(m, "status")
	switch status {
	case "ack":
		return Ack{}, nil
	case "fails":
		if propType := getString(m, "type"); propType != "property" {
			return nil, protocolError(fmt.Sprintf("expected type \"property\" in violation response, got %q", propType))
		}
		idx, err := parseNumberAsInt64(m["property_index"])
		if err != nil {
			return nil, wrapProtocolError("invalid property_index", err)
		}
		if idx < 0 {
			return nil, protocolError(fmt.Sprintf("negative property_index: %d", idx))
		}
		ts, err := parseNumberAsInt64(m["timestamp"])
		if err != nil {
			return nil, wrapProtocolError("invalid timestamp", err)
		}
		if ts < 0 {
			return nil, protocolError(fmt.Sprintf("negative timestamp: %d", ts))
		}
		reason := getString(m, "reason")
		return Violation{
			PropertyIndex: PropertyIndex(idx),
			Timestamp:     Timestamp{Microseconds: ts},
			Reason:        reason,
		}, nil
	case "error":
		code := getString(m, "code")
		msg := getString(m, "message")
		if code != "" {
			return nil, newCodedError(ErrProtocol, code, msg)
		}
		return nil, protocolError(msg)
	default:
		return nil, protocolError(fmt.Sprintf("unexpected frame status: %q", status))
	}
}

// parseStreamResponse decodes an endStream response — a list of final
// property verdicts (Satisfaction / Violation / Unresolved).
func parseStreamResponse(raw string) (*StreamResult, error) {
	m, err := parseResponse(raw)
	if err != nil {
		return nil, err
	}
	if err := checkErrorStatus(m); err != nil {
		return nil, err
	}

	status := getString(m, "status")
	if status != "complete" {
		return nil, protocolError(fmt.Sprintf("expected complete response, got status: %q", status))
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
	return &StreamResult{Results: results}, nil
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
	m, err := parseResponse(raw)
	if err != nil {
		return nil, err
	}
	if err := checkErrorStatus(m); err != nil {
		return nil, err
	}
	status := getString(m, "status")
	if status != "success" {
		return nil, protocolError(fmt.Sprintf("expected success response, got status: %q", status))
	}

	dbcRaw := getObject(m, "dbc")
	if dbcRaw == nil {
		return nil, protocolError("missing 'dbc' field in response")
	}
	return parseDBCDefinition(dbcRaw)
}

// parseDBCTextResponse decodes a formatDBCText response into the .dbc text
// image.  Errors (Agda-side JSON parse failure on the input or unexpected
// status) short-circuit to the (string, error) tuple's error half.
func parseDBCTextResponse(raw string) (string, error) {
	m, err := parseResponse(raw)
	if err != nil {
		return "", err
	}
	if err := checkErrorStatus(m); err != nil {
		return "", err
	}
	status := getString(m, "status")
	if status != "success" {
		return "", protocolError(fmt.Sprintf("expected success response, got status: %q", status))
	}
	text, ok := m["text"].(string)
	if !ok {
		return "", protocolError("missing or non-string 'text' field in formatDBCText response")
	}
	return text, nil
}

// parseParsedDBCResponse decodes a parseDBC / parseDBCText success response
// into typed (*ParsedDBC) form: the parsed body plus any non-error issues
// (warnings).  Errors short-circuit to the (*ParsedDBC, error) tuple's
// error half.
func parseParsedDBCResponse(raw string) (*ParsedDBC, error) {
	m, err := parseResponse(raw)
	if err != nil {
		return nil, err
	}
	if err := checkErrorStatus(m); err != nil {
		return nil, err
	}
	status := getString(m, "status")
	if status != "success" {
		return nil, protocolError(fmt.Sprintf("expected success response, got status: %q", status))
	}

	dbcRaw := getObject(m, "dbc")
	if dbcRaw == nil {
		return nil, protocolError("missing 'dbc' field in parseDBC response")
	}
	dbc, err := parseDBCDefinition(dbcRaw)
	if err != nil {
		return nil, err
	}

	// Initialize empty (not nil) so JSON marshaling produces "[]" instead
	// of "null"; matches Python's empty-list default per
	// feedback_cross_language_parity.md (R18 cluster 5 cross-binding test
	// caught the nil-vs-empty drift).
	warnings := []ValidationIssue{}
	for _, item := range getArray(m, "warnings") {
		issue, ok := item.(map[string]any)
		if !ok {
			return nil, protocolError("expected object in warnings array")
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
		warnings = append(warnings, ValidationIssue{
			Severity: sev,
			Code:     code,
			Detail:   getString(issue, "detail"),
		})
	}
	return &ParsedDBC{DBC: *dbc, Warnings: warnings}, nil
}

// parseDBCDefinition decodes the "dbc" sub-object of a formatDBC
// response into its typed DBCDefinition form. Tier 1 metadata arrays
// (signalGroups / environmentVars / valueTables) are optional on the
// wire — absent or null keys become empty slices.
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

// parseObjects is the shared template for decoding an array-of-objects field
// on the JSON wire.  Returns (nil, nil) for an empty/absent field, a protocol
// error at the first non-object entry, and propagates per-entry decoder
// errors verbatim.  The 7 list parsers in this file (parseSignalGroups /
// parseEnvironmentVars / parseValueTables / parseNodes / parseComments /
// parseAttributes / parseUnresolvedValueDescs) all share this outer
// plumbing; their per-entry decode is the `decode` callback.
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

// parseUnresolvedValueDescs decodes the optional "unresolvedValueDescs" array
// (Track E.8 Plan B). Each entry is `{id, [extended], signalName, entries}`.
// Empty/absent on the JSON-parse path is the common case.
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

// parseEnvironmentVars decodes the optional "environmentVars" array.
// The wire-tag “varType“ must be one of 0/1/2 (Int/Float/String); any
// other value is a protocol error.
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

// parseValueTables decodes the optional "valueTables" array. Each entry's
// integer value is parsed through [parseNumberAsInt64] to tolerate JSON's
// float decoder on whole-number values.
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

// --- Tier 2 parsers (JSON from Agda core → Go) ---

// parseNodes decodes the optional "nodes" array.
func parseNodes(j map[string]any) ([]DBCNode, error) {
	return parseObjects(j, "nodes", func(nRaw map[string]any) (DBCNode, error) {
		return DBCNode{Name: getString(nRaw, "name")}, nil
	})
}

// parseCanIDFields reads the {"id", "extended"} pair that every
// message/signal-scoped tagged target embeds. "extended" is NotRequired
// on the wire — absent means standard (11-bit) ID.
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

// parseCommentTarget decodes one comment target object, dispatching on
// the "kind" discriminator and rejecting unknown kinds as protocol
// errors (matches Agda's parseCommentTarget).
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
	extended := getBool(j, "extended")

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
	switch getString(j, "byteOrder") {
	case "little_endian":
		bo = LittleEndian
	case "big_endian":
		bo = BigEndian
	default:
		return zero, protocolError(fmt.Sprintf("unrecognized byte order: %q", getString(j, "byteOrder")))
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
	if length < 1 || length > 64 {
		return zero, protocolError(fmt.Sprintf("bit length %d out of range (1-64)", length))
	}

	presence, err := parseSignalPresence(j)
	if err != nil {
		return zero, err
	}

	name := getString(j, "name")
	if name == "" {
		return zero, protocolError("signal missing required field: name")
	}

	// Explicit lookup: "signed" must be present in well-formed DBC JSON
	// from the Agda parser. Default to false (unsigned, the CAN standard
	// default) but log a warning via error return if missing.
	signedVal, signedOk := j["signed"]
	isSigned := false
	if signedOk {
		if b, ok := signedVal.(bool); ok {
			isSigned = b
		}
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

// parseSignalPresence decodes the multiplexor "presence" object that
// names the multiplexor signal plus the mux values under which a
// multiplexed signal is active.
func parseSignalPresence(j map[string]any) (SignalPresence, error) {
	muxName := getString(j, "multiplexor")
	if muxName == "" {
		return AlwaysPresent{}, nil
	}
	rawVals, ok := j["multiplex_values"].([]any)
	if !ok || len(rawVals) == 0 {
		return nil, protocolError("multiplex_values must be a non-empty array")
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
		Multiplexor: SignalName(muxName),
		MuxValues:   muxVals,
	}, nil
}
