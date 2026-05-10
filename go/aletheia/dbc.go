package aletheia

import "fmt"

// SignalPresence describes when a signal is present in a frame.
type SignalPresence interface {
	signalPresence() // sealed
}

// AlwaysPresent means the signal is in every frame of its message.
type AlwaysPresent struct{}

func (AlwaysPresent) signalPresence() {}

// Multiplexed means the signal is present only when a multiplexor has one of the specified values.
type Multiplexed struct {
	Multiplexor SignalName
	MuxValues   []MultiplexValue
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
	// Receivers is the trailing node list from the SG_ line. The
	// Vector__XXX DBC placeholder is stripped on parse; an empty
	// slice round-trips back to Vector__XXX on re-emission.
	Receivers []string
	// ValueDescriptions carries the inline VAL_ entries attached to this
	// signal. Empty when no VAL_ line names the signal. Same
	// (value, description) shape as DBCValueTable.Entries — the wire emits
	// both as ordered arrays.
	ValueDescriptions []DBCValueEntry
}

// DBCMessage defines a CAN message with its signals.
type DBCMessage struct {
	ID     CANID
	Name   MessageName
	DLC    DLC
	Sender NodeName
	// Senders carries the additional transmitters declared on BO_TX_BU_
	// lines. The BO_ primary stays in Sender; these extras feed the Agda
	// validator's UnknownMessageSender check with the "additional sender"
	// disambiguation so primary-vs-extra diagnostics stay distinguishable.
	Senders     []string
	Signals     []DBCSignal
	signalIndex map[string]int // maps signal name -> index into Signals
}

// NewDbcMessage creates a [DBCMessage] with its signal-name lookup index
// populated. External loaders must use this constructor — directly populating
// the struct leaves signalIndex nil and forces [DBCMessage.SignalByName] onto
// its linear fallback path.
//
// senders carries the BO_TX_BU_ additional-transmitter list; pass nil or an
// empty slice when the DBC source has no BO_TX_BU_ line for this message.
func NewDbcMessage(id CANID, name MessageName, dlc DLC, sender NodeName, senders []string, signals []DBCSignal) DBCMessage {
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

// ---------------------------------------------------------------------------
// Multiplexing query helpers
// ---------------------------------------------------------------------------

// IsMultiplexed reports whether this message contains any multiplexed signals.
func (m DBCMessage) IsMultiplexed() bool {
	for _, s := range m.Signals {
		if _, ok := s.Presence.(Multiplexed); ok {
			return true
		}
	}
	return false
}

// AlwaysPresentSignals returns signals that are present in every frame.
func (m DBCMessage) AlwaysPresentSignals() []DBCSignal {
	var out []DBCSignal
	for _, s := range m.Signals {
		if _, ok := s.Presence.(AlwaysPresent); ok {
			out = append(out, s)
		}
	}
	return out
}

// MultiplexedSignals returns signals that are conditionally present
// (present only when their multiplexor has a specific value).
func (m DBCMessage) MultiplexedSignals() []DBCSignal {
	var out []DBCSignal
	for _, s := range m.Signals {
		if _, ok := s.Presence.(Multiplexed); ok {
			out = append(out, s)
		}
	}
	return out
}

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

// MuxValues returns all multiplex values associated with the given multiplexor
// signal, sorted by order of first occurrence. Returns nil if no multiplexed
// signals reference the given multiplexor.
func (m DBCMessage) MuxValues(multiplexor SignalName) []MultiplexValue {
	seen := make(map[MultiplexValue]bool)
	var out []MultiplexValue
	for _, s := range m.Signals {
		if mux, ok := s.Presence.(Multiplexed); ok && mux.Multiplexor == multiplexor {
			for _, v := range mux.MuxValues {
				if !seen[v] {
					seen[v] = true
					out = append(out, v)
				}
			}
		}
	}
	return out
}

// SignalsForMuxValue returns signals present when the given multiplexor has the
// given value. This includes all always-present signals plus multiplexed signals
// matching the multiplexor and value.
func (m DBCMessage) SignalsForMuxValue(multiplexor SignalName, value MultiplexValue) []DBCSignal {
	var out []DBCSignal
	for _, s := range m.Signals {
		switch p := s.Presence.(type) {
		case AlwaysPresent:
			out = append(out, s)
		case Multiplexed:
			if p.Multiplexor == multiplexor && ContainsMuxValue(p.MuxValues, value) {
				out = append(out, s)
			}
		}
	}
	return out
}

// ContainsMuxValue reports whether vals contains v. Exposed for external loader
// subpackages (e.g. the separate excel module) that inspect Multiplexed presence.
func ContainsMuxValue(vals []MultiplexValue, v MultiplexValue) bool {
	for _, mv := range vals {
		if mv == v {
			return true
		}
	}
	return false
}

// SignalByName returns a deep copy of the first signal with the given name,
// or nil if not found.
func (m DBCMessage) SignalByName(name SignalName) *DBCSignal {
	if m.signalIndex != nil {
		if idx, ok := m.signalIndex[string(name)]; ok {
			out := m.Signals[idx]
			return &out
		}
		return nil
	}
	// Fallback for manually-constructed messages without index.
	for i := range m.Signals {
		if m.Signals[i].Name == name {
			out := m.Signals[i]
			return &out
		}
	}
	return nil
}

// ---------------------------------------------------------------------------
// DBC signal group (SIG_GROUP_ keyword)
//
// The DBC spec carries a parent-message id and a repetition count on the
// wire; the Agda core only models the flattened {name, signals} view
// because signal-name uniqueness is enforced globally by the validator, so
// reconstructing message context on format_dbc is unnecessary.
// ---------------------------------------------------------------------------

// DBCSignalGroup is a DBC signal group (SIG_GROUP_ keyword).
type DBCSignalGroup struct {
	Name    string
	Signals []SignalName
}

// ---------------------------------------------------------------------------
// DBC environment variable (EV_ keyword)
//
// The DBC spec encodes int/float/string as 0/1/2 respectively on the wire;
// the Agda core preserves that vocabulary directly (varTypeToℕ).
// ---------------------------------------------------------------------------

// DBCVarType is the integer tag of a DBC environment variable's declared
// type. Values other than the three listed are rejected by parseDbcDefinition
// as a protocol error.
type DBCVarType int

// DBC var type constants (wire tag values).
const (
	// DBCVarTypeInt — integer-valued environment variable (DBC `0`).
	DBCVarTypeInt DBCVarType = 0
	// DBCVarTypeFloat — float-valued environment variable (DBC `1`).
	DBCVarTypeFloat DBCVarType = 1
	// DBCVarTypeString — string-valued environment variable (DBC `2`).
	DBCVarTypeString DBCVarType = 2
)

// String returns a human-readable name for this var type.  Cross-binding
// parity with ByteOrder.String / IssueSeverity.String / Verdict.String;
// R19 cluster 10 — GO-D-15.3.
func (v DBCVarType) String() string {
	switch v {
	case DBCVarTypeInt:
		return "int"
	case DBCVarTypeFloat:
		return "float"
	case DBCVarTypeString:
		return "string"
	default:
		return fmt.Sprintf("DBCVarType(%d)", int(v))
	}
}

// DBCEnvironmentVar is a DBC environment variable (EV_ keyword).
// Numeric fields use [Rational] to preserve exact decimal intent through
// the wire round-trip, matching the Agda core's ℚ representation.
type DBCEnvironmentVar struct {
	Name    string
	VarType DBCVarType
	Initial Rational
	Minimum Rational
	Maximum Rational
}

// ---------------------------------------------------------------------------
// DBC value table (VAL_TABLE_ keyword)
// ---------------------------------------------------------------------------

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

// DBCRawValueDesc is one unresolved VAL_ line from the DBC text-parse path
// (Track E.8, Plan B).  Carries the owning message's CAN ID, the signal
// name, and the value-label entries.  Populated only when the text-parse
// path encounters a VAL_ line whose (canId, signalName) pair did not match
// any signal in the parsed messages; the entries are preserved verbatim so
// the validator's CHECK 23 UnknownValueDescriptionTarget can warn at
// validation time.
type DBCRawValueDesc struct {
	CANID      CANID
	SignalName string
	Entries    []DBCValueEntry
}

// ---------------------------------------------------------------------------
// Tier 2 DBC metadata: nodes (BU_), comments (CM_), attributes (BA_*)
//
// Every tagged wire object uses "kind" as the first-field discriminator;
// Go has no sum types so each family is modelled as a sealed interface
// with one concrete struct per variant (matching the SignalPresence
// pattern already in use for always-vs-multiplexed signals).
// ---------------------------------------------------------------------------

// DBCNode is a DBC network node (BU_ keyword).
type DBCNode struct {
	Name string
}

// --- Comment targets (CM_ family) ---

// DBCCommentTarget is the sealed sum of the 5 comment-target kinds.
type DBCCommentTarget interface {
	commentTarget() // sealed
}

// DBCCommentTargetNetwork is a network-wide comment.
type DBCCommentTargetNetwork struct{}

func (DBCCommentTargetNetwork) commentTarget() {}

// DBCCommentTargetNode is a node comment.
type DBCCommentTargetNode struct {
	Node string
}

func (DBCCommentTargetNode) commentTarget() {}

// DBCCommentTargetMessage is a message comment. Extended is emitted on
// the wire only when true, matching Agda's formatCANId which omits the
// field for 11-bit standard IDs.
type DBCCommentTargetMessage struct {
	ID       uint32
	Extended bool
}

func (DBCCommentTargetMessage) commentTarget() {}

// DBCCommentTargetSignal is a signal comment.
type DBCCommentTargetSignal struct {
	ID       uint32
	Extended bool
	Signal   string
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

// --- Attribute scope (BA_DEF_ keyword class) ---

// DBCAttrScope names the scope of a BA_DEF_ attribute declaration.
type DBCAttrScope int

// Attribute scope constants matching Agda AttrScope. The nodeMsg /
// nodeSig entries are the relational scopes introduced by BA_DEF_REL_
// (BU_BO_REL_ / BU_SG_REL_ in DBC text).
const (
	// DBCAttrScopeNetwork — attribute applies to the network as a whole (`""` in BA_DEF_).
	DBCAttrScopeNetwork DBCAttrScope = iota
	// DBCAttrScopeNode — attribute scoped to a node (`BU_` in BA_DEF_).
	DBCAttrScopeNode
	// DBCAttrScopeMessage — attribute scoped to a message (`BO_` in BA_DEF_).
	DBCAttrScopeMessage
	// DBCAttrScopeSignal — attribute scoped to a signal (`SG_` in BA_DEF_).
	DBCAttrScopeSignal
	// DBCAttrScopeEnvVar — attribute scoped to an environment variable (`EV_` in BA_DEF_).
	DBCAttrScopeEnvVar
	// DBCAttrScopeNodeMsg — relational scope: (node, message) pair (`BU_BO_REL_` in BA_DEF_REL_).
	DBCAttrScopeNodeMsg
	// DBCAttrScopeNodeSig — relational scope: (node, signal) pair (`BU_SG_REL_` in BA_DEF_REL_).
	DBCAttrScopeNodeSig
)

// String returns the DBC keyword form of this scope ("", "BU_", "BO_",
// "SG_", "EV_", "BU_BO_REL_", "BU_SG_REL_").  Cross-binding parity with
// ByteOrder.String / DBCVarType.String / IssueSeverity.String /
// Verdict.String; R19 cluster 10 — GO-D-15.3.
func (s DBCAttrScope) String() string {
	switch s {
	case DBCAttrScopeNetwork:
		return ""
	case DBCAttrScopeNode:
		return "BU_"
	case DBCAttrScopeMessage:
		return "BO_"
	case DBCAttrScopeSignal:
		return "SG_"
	case DBCAttrScopeEnvVar:
		return "EV_"
	case DBCAttrScopeNodeMsg:
		return "BU_BO_REL_"
	case DBCAttrScopeNodeSig:
		return "BU_SG_REL_"
	default:
		return fmt.Sprintf("DBCAttrScope(%d)", int(s))
	}
}

// --- Attribute types (RHS of BA_DEF_) ---

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

// DBCAttrTypeFloat is a float attribute definition. Bounds use Rational
// to mirror Python's Fraction and preserve ℚ precision end-to-end —
// float64 would drift when a DBC text input carries a non-terminating
// binary fraction.
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

// --- Attribute values (BA_, BA_REL_, BA_DEF_DEF_) ---

// DBCAttrValue is the sealed sum of the 5 attribute-value kinds.
type DBCAttrValue interface {
	attrValue() // sealed
}

// DBCAttrValueInt is an integer attribute value.
type DBCAttrValueInt struct {
	Value int64
}

func (DBCAttrValueInt) attrValue() {}

// DBCAttrValueFloat is a float attribute value. Same Rational-over-double
// rationale as DBCAttrTypeFloat above.
type DBCAttrValueFloat struct {
	Value Rational
}

func (DBCAttrValueFloat) attrValue() {}

// DBCAttrValueString is a string attribute value.
type DBCAttrValueString struct {
	Value string
}

func (DBCAttrValueString) attrValue() {}

// DBCAttrValueEnum is an enum attribute value carrying the ℕ index of
// the chosen label in the corresponding DBCAttrTypeEnum.Values list.
type DBCAttrValueEnum struct {
	Value int64
}

func (DBCAttrValueEnum) attrValue() {}

// DBCAttrValueHex is a hex attribute value.
type DBCAttrValueHex struct {
	Value int64
}

func (DBCAttrValueHex) attrValue() {}

// --- Attribute assignment targets (LHS of BA_ / BA_REL_) ---

// DBCAttrTarget is the sealed sum of the 7 attribute-target kinds.
type DBCAttrTarget interface {
	attrTarget() // sealed
}

// DBCAttrTargetNetwork is a network-scope assignment.
type DBCAttrTargetNetwork struct{}

func (DBCAttrTargetNetwork) attrTarget() {}

// DBCAttrTargetNode is a node-scope assignment.
type DBCAttrTargetNode struct {
	Node string
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
	Signal   string
}

func (DBCAttrTargetSignal) attrTarget() {}

// DBCAttrTargetEnvVar is an env-var-scope assignment.
type DBCAttrTargetEnvVar struct {
	EnvVar string
}

func (DBCAttrTargetEnvVar) attrTarget() {}

// DBCAttrTargetNodeMsg is a node-message relational assignment.
type DBCAttrTargetNodeMsg struct {
	Node     string
	ID       uint32
	Extended bool
}

func (DBCAttrTargetNodeMsg) attrTarget() {}

// DBCAttrTargetNodeSig is a node-signal relational assignment.
type DBCAttrTargetNodeSig struct {
	Node     string
	ID       uint32
	Extended bool
	Signal   string
}

func (DBCAttrTargetNodeSig) attrTarget() {}

// --- Attribute ADT (3 variants: BA_DEF_ / BA_DEF_DEF_ / BA_) ---

// DBCAttribute is the sealed sum of the 3 BA_* entry kinds. Wire
// ordering (definition → default → assignment) is preserved because all
// three variants live in a single flat list.
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

// ---------------------------------------------------------------------------
// DBC definition and lookup helpers
// ---------------------------------------------------------------------------

// DBCDefinition is a complete DBC database.
//
// Tier 1 metadata slices (SignalGroups / EnvironmentVars / ValueTables)
// mirror the Agda DBC record fields 3-5; Tier 2 slices (Nodes / Comments
// / Attributes) mirror fields 6-8. All six are written on every
// format_dbc response even when empty, matching the C++ and Python
// bindings.
type DBCDefinition struct {
	Version         string
	Messages        []DBCMessage
	SignalGroups    []DBCSignalGroup
	EnvironmentVars []DBCEnvironmentVar
	ValueTables     []DBCValueTable
	Nodes           []DBCNode
	Comments        []DBCComment
	Attributes      []DBCAttribute
	// Track E.8 (Plan B): VAL_ entries from the text-parse path that did
	// not resolve to any signal in Messages. Empty on the JSON-parse path.
	UnresolvedValueDescriptions []DBCRawValueDesc
	nameIndex                   map[string]int // maps message name -> index
	idIndex                     map[uint64]int // maps composite CAN ID key -> index
}

// NewDbcDefinition creates a [DBCDefinition] with its message-name and
// CAN-ID lookup indexes populated. External loaders must use this
// constructor — directly populating the struct leaves the indexes nil and
// forces [DBCDefinition.MessageByID] and [DBCDefinition.MessageByName] onto
// their linear fallback paths.
func NewDbcDefinition(version string, messages []DBCMessage) *DBCDefinition {
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

// canIDKey returns a uint64 key that encodes both the CAN ID value and its type
// (standard vs extended) for use as a map key.
func canIDKey(id CANID) uint64 {
	k := uint64(id.Value())
	if id.IsExtended() {
		k |= extendedIDFlag
	}
	return k
}

// MessageByID returns the first message with the given CAN ID, or nil if not found.
// The returned pointer is a deep copy; mutating it does not affect the DBCDefinition.
func (d *DBCDefinition) MessageByID(id CANID) *DBCMessage {
	if d.idIndex != nil {
		if idx, ok := d.idIndex[canIDKey(id)]; ok {
			return copyMessage(&d.Messages[idx])
		}
		return nil
	}
	// Fallback for manually-constructed definitions without index.
	for i := range d.Messages {
		if d.Messages[i].ID.Value() == id.Value() && d.Messages[i].ID.IsExtended() == id.IsExtended() {
			return copyMessage(&d.Messages[i])
		}
	}
	return nil
}

// MessageByName returns the first message with the given name, or nil if not found.
// The returned pointer is a deep copy; mutating it does not affect the DBCDefinition.
func (d *DBCDefinition) MessageByName(name MessageName) *DBCMessage {
	if d.nameIndex != nil {
		if idx, ok := d.nameIndex[string(name)]; ok {
			return copyMessage(&d.Messages[idx])
		}
		return nil
	}
	// Fallback for manually-constructed definitions without index.
	for i := range d.Messages {
		if d.Messages[i].Name == name {
			return copyMessage(&d.Messages[i])
		}
	}
	return nil
}

// copyMessage returns a deep copy of a DBCMessage, including its Signals slice.
func copyMessage(m *DBCMessage) *DBCMessage {
	out := *m
	out.Signals = append([]DBCSignal(nil), m.Signals...)
	return &out
}
