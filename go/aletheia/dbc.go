// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import "slices"

// SignalPresence describes when a signal is present in a frame.
type SignalPresence interface {
	signalPresence() // sealed
}

// AlwaysPresent means the signal is in every frame of its message.
type AlwaysPresent struct{}

func (AlwaysPresent) signalPresence() {}

// Multiplexed means the signal is present only when a multiplexor has one of the specified values.
type Multiplexed struct {
	Multiplexor     SignalName
	MultiplexValues []MultiplexValue
}

func (Multiplexed) signalPresence() {}

// DBCSignal defines a single signal within a DBC message.
type DBCSignal struct {
	Name      SignalName
	StartBit  BitPosition
	BitLength BitLength
	ByteOrder ByteOrder
	IsSigned  bool
	Factor    Rational
	Offset    Rational
	Minimum   Rational
	Maximum   Rational
	Unit      Unit
	Presence  SignalPresence
	// Receivers is the SG_ line's trailing node list; the Vector__XXX
	// placeholder is stripped on parse and written back for an empty list.
	Receivers []NodeName
	// ValueDescriptions holds the VAL_ entries naming this signal, in the
	// (value, description) shape of DBCValueTable.Entries.
	ValueDescriptions []DBCValueEntry
}

// DBCMessage defines a CAN message with its signals.
type DBCMessage struct {
	ID     CANID
	Name   MessageName
	DLC    DLC
	Sender NodeName
	// Senders holds the additional transmitters of BO_TX_BU_ lines; the BO_
	// primary stays in Sender, so the validator can tell the two apart in
	// its unknown-sender diagnostics.
	Senders     []NodeName
	Signals     []DBCSignal
	signalIndex map[string]int // maps signal name -> index into Signals
}

// NewDBCMessage creates a [DBCMessage] with its signal-name index built; a
// message populated by hand has no index and [DBCMessage.SignalByName]
// scans instead. senders is the BO_TX_BU_ list, nil when the source has
// none.
func NewDBCMessage(id CANID, name MessageName, dlc DLC, sender NodeName, senders []NodeName, signals []DBCSignal) DBCMessage {
	m := DBCMessage{
		ID:      id,
		Name:    name,
		DLC:     dlc,
		Sender:  sender,
		Senders: senders,
		Signals: signals,
	}
	m.buildSignalIndex()
	return m
}

// buildSignalIndex populates the signal name lookup index.
func (m *DBCMessage) buildSignalIndex() {
	m.signalIndex = make(map[string]int, len(m.Signals))
	for i := range m.Signals {
		m.signalIndex[string(m.Signals[i].Name)] = i
	}
}

func isAlwaysPresent(s DBCSignal) bool { _, ok := s.Presence.(AlwaysPresent); return ok }
func isMultiplexed(s DBCSignal) bool   { _, ok := s.Presence.(Multiplexed); return ok }

// signalsWhere returns the signals satisfying keep, in message order; nil when none.
func (m DBCMessage) signalsWhere(keep func(DBCSignal) bool) []DBCSignal {
	var out []DBCSignal
	for _, s := range m.Signals {
		if keep(s) {
			out = append(out, s)
		}
	}
	return out
}

// IsMultiplexed reports whether any signal of the message is multiplexed.
func (m DBCMessage) IsMultiplexed() bool { return slices.ContainsFunc(m.Signals, isMultiplexed) }

// AlwaysPresentSignals returns the signals present in every frame.
func (m DBCMessage) AlwaysPresentSignals() []DBCSignal { return m.signalsWhere(isAlwaysPresent) }

// MultiplexedSignals returns the signals present only for some multiplexor values.
func (m DBCMessage) MultiplexedSignals() []DBCSignal { return m.signalsWhere(isMultiplexed) }

// MultiplexorNames returns the distinct multiplexor signal names referenced by
// multiplexed signals in this message, in order of first occurrence.
func (m DBCMessage) MultiplexorNames() []SignalName {
	seen := make(map[SignalName]bool)
	var out []SignalName
	for _, s := range m.Signals {
		if mux, ok := s.Presence.(Multiplexed); ok {
			if !seen[mux.Multiplexor] {
				seen[mux.Multiplexor] = true
				out = append(out, mux.Multiplexor)
			}
		}
	}
	return out
}

// MultiplexValues returns all multiplex values associated with the given multiplexor
// signal, sorted by order of first occurrence. Returns nil if no multiplexed
// signals reference the given multiplexor.
func (m DBCMessage) MultiplexValues(multiplexor SignalName) []MultiplexValue {
	seen := make(map[MultiplexValue]bool)
	var out []MultiplexValue
	for _, s := range m.Signals {
		if mux, ok := s.Presence.(Multiplexed); ok && mux.Multiplexor == multiplexor {
			for _, v := range mux.MultiplexValues {
				if !seen[v] {
					seen[v] = true
					out = append(out, v)
				}
			}
		}
	}
	return out
}

// SignalsForMuxValue returns the signals present when the multiplexor has the
// value: every always-present signal, and the multiplexed signals selected by
// that multiplexor and value.
func (m DBCMessage) SignalsForMuxValue(multiplexor SignalName, value MultiplexValue) []DBCSignal {
	return m.signalsWhere(func(s DBCSignal) bool {
		switch p := s.Presence.(type) {
		case AlwaysPresent:
			return true
		case Multiplexed:
			return p.Multiplexor == multiplexor && ContainsMuxValue(p.MultiplexValues, value)
		}
		return false
	})
}

// ContainsMuxValue reports whether vals contains v; the separate excel module
// inspects Multiplexed presence through it.
func ContainsMuxValue(vals []MultiplexValue, v MultiplexValue) bool { return slices.Contains(vals, v) }

// lookup finds the element at key: through the index when the message or
// definition has one, else by scanning the n elements. A cached position is
// trusted only while it is in range and matches still holds there, since the
// public slice may have been shrunk, reordered or overwritten since the
// index was built; a stale position reads as not found. Returns -1 for
// not found.
func lookup[K comparable](index map[K]int, key K, n int, matches func(int) bool) int {
	if index != nil {
		if idx, ok := index[key]; ok && idx < n && matches(idx) {
			return idx
		}
		return -1
	}
	for i := range n {
		if matches(i) {
			return i
		}
	}
	return -1
}

// SignalByName returns a copy of the signal with the given name, or nil.
// Duplicate signal names are a validation issue; which duplicate a
// hand-built message returns is unspecified. The copy is shallow: its
// Receivers, ValueDescriptions and MultiplexValues slices alias the
// message's.
func (m DBCMessage) SignalByName(name SignalName) *DBCSignal {
	i := lookup(m.signalIndex, string(name), len(m.Signals), func(i int) bool { return m.Signals[i].Name == name })
	if i < 0 {
		return nil
	}
	out := m.Signals[i]
	return &out
}

// DBCSignalGroup is a DBC signal group (SIG_GROUP_ keyword). The DBC text
// carries a parent message id and a repetition count too; the core's
// SignalGroup keeps only the name and the signals, since the validator
// enforces signal-name uniqueness globally.
type DBCSignalGroup struct {
	Name    string
	Signals []SignalName
}

// DBCVarType is the integer tag of an environment variable's declared type,
// the DBC text's own 0, 1 and 2 for int, float and string, which the core
// keeps (varTypeToℕ). Any other value is a protocol error in
// parseDBCDefinition.
type DBCVarType int

//go:generate stringer -type=DBCVarType -linecomment -output=dbcvartype_string.go

const (
	// DBCVarTypeInt is an integer-valued environment variable.
	DBCVarTypeInt DBCVarType = 0 // int
	// DBCVarTypeFloat is a float-valued environment variable.
	DBCVarTypeFloat DBCVarType = 1 // float
	// DBCVarTypeString is a string-valued environment variable.
	DBCVarTypeString DBCVarType = 2 // string
)

// DBCEnvironmentVar is a DBC environment variable (EV_ keyword); its
// numeric fields are [Rational], as the core holds them.
type DBCEnvironmentVar struct {
	Name    string
	VarType DBCVarType
	Initial Rational
	Minimum Rational
	Maximum Rational
}

// DBCValueEntry is one (value, description) pair in a [DBCValueTable].
type DBCValueEntry struct {
	Value       int64
	Description string
}

// DBCValueTable is a DBC value table (VAL_TABLE_ keyword).
type DBCValueTable struct {
	Name    string
	Entries []DBCValueEntry
}

// DBCRawValueDesc is a VAL_ line of the text-parse path whose CAN ID and
// signal name matched no parsed signal, kept whole so the validator's
// UnknownValueDescriptionTarget check can warn about it.
type DBCRawValueDesc struct {
	ID         CANID
	SignalName SignalName
	Entries    []DBCValueEntry
}

// The tier 2 metadata (nodes, comments, attributes) arrives as tagged wire
// objects with "kind" as the first field; each family is a sealed
// interface with one struct per variant, as SignalPresence is.

// DBCNode is a DBC network node (BU_ keyword).
type DBCNode struct {
	Name NodeName
}

// DBCCommentTarget is the sealed sum of the 5 comment-target kinds.
type DBCCommentTarget interface {
	commentTarget() // sealed
}

// DBCCommentTargetNetwork is a network-wide comment.
type DBCCommentTargetNetwork struct{}

func (DBCCommentTargetNetwork) commentTarget() {}

// DBCCommentTargetNode is a node comment.
type DBCCommentTargetNode struct {
	Node NodeName
}

func (DBCCommentTargetNode) commentTarget() {}

// DBCCommentTargetMessage is a message comment. The identifier is the type
// the rest of the package uses, which refuses an out-of-range value at
// construction, so a comment cannot name a message no frame could carry. The
// wire writes the extended flag only when true, as the core's formatCANId
// omits it for a standard ID.
type DBCCommentTargetMessage struct {
	ID CANID
}

func (DBCCommentTargetMessage) commentTarget() {}

// DBCCommentTargetSignal is a signal comment.
type DBCCommentTargetSignal struct {
	ID     CANID
	Signal SignalName
}

func (DBCCommentTargetSignal) commentTarget() {}

// DBCCommentTargetEnvVar is an environment-variable comment.
type DBCCommentTargetEnvVar struct {
	EnvVar string
}

func (DBCCommentTargetEnvVar) commentTarget() {}

// DBCComment is one CM_ entry with its target and body.
type DBCComment struct {
	Target DBCCommentTarget
	Text   string
}

// DBCAttrScope names the scope of a BA_DEF_ attribute declaration.
type DBCAttrScope int

//go:generate stringer -type=DBCAttrScope -linecomment -output=dbcattrscope_string.go

// The scopes are the core's AttrScope; the line comment on each is its
// spelling in BA_DEF_ (or BA_DEF_REL_ for the two relational scopes).
const (
	// DBCAttrScopeNetwork scopes an attribute to the whole network.
	DBCAttrScopeNetwork DBCAttrScope = iota //
	// DBCAttrScopeNode scopes an attribute to a node.
	DBCAttrScopeNode // BU_
	// DBCAttrScopeMessage scopes an attribute to a message.
	DBCAttrScopeMessage // BO_
	// DBCAttrScopeSignal scopes an attribute to a signal.
	DBCAttrScopeSignal // SG_
	// DBCAttrScopeEnvVar scopes an attribute to an environment variable.
	DBCAttrScopeEnvVar // EV_
	// DBCAttrScopeNodeMsg scopes an attribute to a (node, message) pair.
	DBCAttrScopeNodeMsg // BU_BO_REL_
	// DBCAttrScopeNodeSig scopes an attribute to a (node, signal) pair.
	DBCAttrScopeNodeSig // BU_SG_REL_
)

// DBCAttrType is the sealed sum of the 5 attribute-definition kinds.
type DBCAttrType interface {
	attrType() // sealed
}

// DBCAttrTypeInt is an integer attribute definition.
type DBCAttrTypeInt struct {
	Min int64
	Max int64
}

func (DBCAttrTypeInt) attrType() {}

// DBCAttrTypeFloat is a float attribute definition. The bounds are
// Rational, as Python's are Fraction: a float64 would drift on a DBC text
// value with no finite binary expansion.
type DBCAttrTypeFloat struct {
	Min Rational
	Max Rational
}

func (DBCAttrTypeFloat) attrType() {}

// DBCAttrTypeString is a string attribute definition.
type DBCAttrTypeString struct{}

func (DBCAttrTypeString) attrType() {}

// DBCAttrTypeEnum is an enum attribute definition carrying its label set.
type DBCAttrTypeEnum struct {
	Values []string
}

func (DBCAttrTypeEnum) attrType() {}

// DBCAttrTypeHex is a hex attribute definition (unsigned range).
type DBCAttrTypeHex struct {
	Min int64
	Max int64
}

func (DBCAttrTypeHex) attrType() {}

// DBCAttrValue is the sealed sum of the 5 attribute-value kinds.
type DBCAttrValue interface {
	attrValue() // sealed
}

// DBCAttrValueInt is an integer attribute value.
type DBCAttrValueInt struct {
	Value int64
}

func (DBCAttrValueInt) attrValue() {}

// DBCAttrValueFloat is a float attribute value, Rational for the reason
// DBCAttrTypeFloat gives.
type DBCAttrValueFloat struct {
	Value Rational
}

func (DBCAttrValueFloat) attrValue() {}

// DBCAttrValueString is a string attribute value.
type DBCAttrValueString struct {
	Value string
}

func (DBCAttrValueString) attrValue() {}

// DBCAttrValueEnum is an enum attribute value: the index of the chosen
// label in the definition's Values.
type DBCAttrValueEnum struct {
	Value int64
}

func (DBCAttrValueEnum) attrValue() {}

// DBCAttrValueHex is a hex attribute value.
type DBCAttrValueHex struct {
	Value int64
}

func (DBCAttrValueHex) attrValue() {}

// DBCAttrTarget is the sealed sum of the 7 attribute-target kinds.
type DBCAttrTarget interface {
	attrTarget() // sealed
}

// DBCAttrTargetNetwork is a network-scope assignment.
type DBCAttrTargetNetwork struct{}

func (DBCAttrTargetNetwork) attrTarget() {}

// DBCAttrTargetNode is a node-scope assignment.
type DBCAttrTargetNode struct {
	Node NodeName
}

func (DBCAttrTargetNode) attrTarget() {}

// DBCAttrTargetMessage is a message-scope assignment.
type DBCAttrTargetMessage struct {
	ID       uint32
	Extended bool
}

func (DBCAttrTargetMessage) attrTarget() {}

// DBCAttrTargetSignal is a signal-scope assignment.
type DBCAttrTargetSignal struct {
	ID       uint32
	Extended bool
	Signal   SignalName
}

func (DBCAttrTargetSignal) attrTarget() {}

// DBCAttrTargetEnvVar is an env-var-scope assignment.
type DBCAttrTargetEnvVar struct {
	EnvVar string
}

func (DBCAttrTargetEnvVar) attrTarget() {}

// DBCAttrTargetNodeMsg is a node-message relational assignment.
type DBCAttrTargetNodeMsg struct {
	Node     NodeName
	ID       uint32
	Extended bool
}

func (DBCAttrTargetNodeMsg) attrTarget() {}

// DBCAttrTargetNodeSig is a node-signal relational assignment.
type DBCAttrTargetNodeSig struct {
	Node     NodeName
	ID       uint32
	Extended bool
	Signal   SignalName
}

func (DBCAttrTargetNodeSig) attrTarget() {}

// DBCAttribute is the sealed sum of the 3 BA_* entry kinds; one flat list
// keeps the wire order of definitions, defaults and assignments.
type DBCAttribute interface {
	attribute() // sealed
}

// DBCAttrDef is an attribute declaration (BA_DEF_ / BA_DEF_REL_).
type DBCAttrDef struct {
	Name     string
	Scope    DBCAttrScope
	AttrType DBCAttrType
}

func (DBCAttrDef) attribute() {}

// DBCAttrDefault is an attribute default (BA_DEF_DEF_ / BA_DEF_DEF_REL_).
type DBCAttrDefault struct {
	Name  string
	Value DBCAttrValue
}

func (DBCAttrDefault) attribute() {}

// DBCAttrAssign is an attribute assignment (BA_ / BA_REL_).
type DBCAttrAssign struct {
	Name   string
	Target DBCAttrTarget
	Value  DBCAttrValue
}

func (DBCAttrAssign) attribute() {}

// DBCDefinition is a complete DBC database. SignalGroups, EnvironmentVars
// and ValueTables are the core record's signalGroups, environmentVars and
// valueTables; Nodes, Comments and Attributes its nodes, comments and
// attributes. Every format_dbc response writes all six, empty or not, as
// the C++ and Python bindings do.
type DBCDefinition struct {
	Version         string
	Messages        []DBCMessage
	SignalGroups    []DBCSignalGroup
	EnvironmentVars []DBCEnvironmentVar
	ValueTables     []DBCValueTable
	Nodes           []DBCNode
	Comments        []DBCComment
	Attributes      []DBCAttribute
	// UnresolvedValueDescriptions are the text-parse path's VAL_ lines that
	// matched no signal; empty on the JSON path.
	UnresolvedValueDescriptions []DBCRawValueDesc
	nameIndex                   map[string]int // maps message name -> index
	idIndex                     map[uint64]int // maps composite CAN ID key -> index
}

// NewDBCDefinition creates a [DBCDefinition] with its name and CAN-ID
// indexes built; a definition populated by hand has none and
// [DBCDefinition.MessageByID] and [DBCDefinition.MessageByName] scan instead.
func NewDBCDefinition(version string, messages []DBCMessage) *DBCDefinition {
	d := &DBCDefinition{Version: version, Messages: messages}
	d.buildIndexes()
	return d
}

// buildIndexes populates the message name and ID lookup indexes.
func (d *DBCDefinition) buildIndexes() {
	d.nameIndex = make(map[string]int, len(d.Messages))
	d.idIndex = make(map[uint64]int, len(d.Messages))
	for i := range d.Messages {
		d.nameIndex[string(d.Messages[i].Name)] = i
		key := canIDKey(d.Messages[i].ID)
		d.idIndex[key] = i
	}
}

const extendedIDFlag = 1 << 32 // bit 32 distinguishes extended from standard IDs in map keys

// canIDKey packs a CAN ID's value and its standard-or-extended kind into one
// map key.
func canIDKey(id CANID) uint64 {
	k := uint64(id.Value())
	if id.IsExtended() {
		k |= extendedIDFlag
	}
	return k
}

// MessageByID returns a deep copy of the message with the given CAN ID, or
// nil. Duplicate IDs are a validation issue; which duplicate a hand-built
// definition returns is unspecified.
func (d *DBCDefinition) MessageByID(id CANID) *DBCMessage {
	key := canIDKey(id)
	return d.messageAt(lookup(d.idIndex, key, len(d.Messages), func(i int) bool { return canIDKey(d.Messages[i].ID) == key }))
}

// MessageByName returns a deep copy of the message with the given name, or
// nil. Duplicate names are a validation issue; which duplicate a hand-built
// definition returns is unspecified.
func (d *DBCDefinition) MessageByName(name MessageName) *DBCMessage {
	return d.messageAt(lookup(d.nameIndex, string(name), len(d.Messages), func(i int) bool { return d.Messages[i].Name == name }))
}

// messageAt is a deep copy of the message at i, or nil for a not-found -1.
func (d *DBCDefinition) messageAt(i int) *DBCMessage {
	if i < 0 {
		return nil
	}
	return copyMessage(&d.Messages[i])
}

// copyMessage returns a deep copy the caller may mutate without reaching the
// stored definition: the Senders and Signals slices, and in each signal the
// Receivers, ValueDescriptions and MultiplexValues slices (whether the
// presence is held by value or by pointer) are cloned; value fields copy
// with the struct. The signalIndex is shared on purpose: it is read-only
// once built, valid for the same-order clone, and SignalByName tolerates a
// stale entry the same way whether shared or cloned.
func copyMessage(m *DBCMessage) *DBCMessage {
	out := *m
	out.Senders = slices.Clone(m.Senders)
	out.Signals = slices.Clone(m.Signals)
	for i := range out.Signals {
		out.Signals[i].Receivers = slices.Clone(m.Signals[i].Receivers)
		out.Signals[i].ValueDescriptions = slices.Clone(m.Signals[i].ValueDescriptions)
		// the pointer form needs a fresh struct so the copy does not alias it
		switch p := out.Signals[i].Presence.(type) {
		case Multiplexed:
			p.MultiplexValues = slices.Clone(p.MultiplexValues)
			out.Signals[i].Presence = p
		case *Multiplexed:
			clone := *p
			clone.MultiplexValues = slices.Clone(clone.MultiplexValues)
			out.Signals[i].Presence = &clone
		}
	}
	return &out
}
