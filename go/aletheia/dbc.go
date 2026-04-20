package aletheia

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

// DbcSignal defines a single signal within a DBC message.
type DbcSignal struct {
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
}

// DbcMessage defines a CAN message with its signals.
type DbcMessage struct {
	ID          CanID
	Name        MessageName
	DLC         DLC
	Sender      NodeName
	Signals     []DbcSignal
	signalIndex map[string]int // maps signal name -> index into Signals
}

// NewDbcMessage creates a [DbcMessage] with its signal-name lookup index
// populated. External loaders must use this constructor — directly populating
// the struct leaves signalIndex nil and forces [DbcMessage.SignalByName] onto
// its linear fallback path.
func NewDbcMessage(id CanID, name MessageName, dlc DLC, sender NodeName, signals []DbcSignal) DbcMessage {
	m := DbcMessage{
		ID:      id,
		Name:    name,
		DLC:     dlc,
		Sender:  sender,
		Signals: signals,
	}
	m.buildSignalIndex()
	return m
}

// buildSignalIndex populates the signal name lookup index.
func (m *DbcMessage) buildSignalIndex() {
	m.signalIndex = make(map[string]int, len(m.Signals))
	for i := range m.Signals {
		m.signalIndex[string(m.Signals[i].Name)] = i
	}
}

// ---------------------------------------------------------------------------
// Multiplexing query helpers
// ---------------------------------------------------------------------------

// IsMultiplexed reports whether this message contains any multiplexed signals.
func (m DbcMessage) IsMultiplexed() bool {
	for _, s := range m.Signals {
		if _, ok := s.Presence.(Multiplexed); ok {
			return true
		}
	}
	return false
}

// AlwaysPresentSignals returns signals that are present in every frame.
func (m DbcMessage) AlwaysPresentSignals() []DbcSignal {
	var out []DbcSignal
	for _, s := range m.Signals {
		if _, ok := s.Presence.(AlwaysPresent); ok {
			out = append(out, s)
		}
	}
	return out
}

// MultiplexedSignals returns signals that are conditionally present
// (present only when their multiplexor has a specific value).
func (m DbcMessage) MultiplexedSignals() []DbcSignal {
	var out []DbcSignal
	for _, s := range m.Signals {
		if _, ok := s.Presence.(Multiplexed); ok {
			out = append(out, s)
		}
	}
	return out
}

// MultiplexorNames returns the distinct multiplexor signal names referenced by
// multiplexed signals in this message, in order of first occurrence.
func (m DbcMessage) MultiplexorNames() []SignalName {
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
func (m DbcMessage) MuxValues(multiplexor SignalName) []MultiplexValue {
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
func (m DbcMessage) SignalsForMuxValue(multiplexor SignalName, value MultiplexValue) []DbcSignal {
	var out []DbcSignal
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
func (m DbcMessage) SignalByName(name SignalName) *DbcSignal {
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

// DbcSignalGroup is a DBC signal group (SIG_GROUP_ keyword).
type DbcSignalGroup struct {
	Name    string
	Signals []SignalName
}

// ---------------------------------------------------------------------------
// DBC environment variable (EV_ keyword)
//
// The DBC spec encodes int/float/string as 0/1/2 respectively on the wire;
// the Agda core preserves that vocabulary directly (varTypeToℕ).
// ---------------------------------------------------------------------------

// DbcVarType is the integer tag of a DBC environment variable's declared
// type. Values other than the three listed are rejected by parseDbcDefinition
// as a protocol error.
type DbcVarType int

// DBC var type constants (wire tag values).
const (
	DbcVarTypeInt    DbcVarType = 0
	DbcVarTypeFloat  DbcVarType = 1
	DbcVarTypeString DbcVarType = 2
)

// DbcEnvironmentVar is a DBC environment variable (EV_ keyword).
// Numeric fields use [Rational] to preserve exact decimal intent through
// the wire round-trip, matching the Agda core's ℚ representation.
type DbcEnvironmentVar struct {
	Name    string
	VarType DbcVarType
	Initial Rational
	Minimum Rational
	Maximum Rational
}

// ---------------------------------------------------------------------------
// DBC value table (VAL_TABLE_ keyword)
// ---------------------------------------------------------------------------

// DbcValueEntry is one (value, description) pair in a [DbcValueTable].
type DbcValueEntry struct {
	Value       int64
	Description string
}

// DbcValueTable is a DBC value table (VAL_TABLE_ keyword).
type DbcValueTable struct {
	Name    string
	Entries []DbcValueEntry
}

// ---------------------------------------------------------------------------
// Tier 2 DBC metadata: nodes (BU_), comments (CM_), attributes (BA_*)
//
// Every tagged wire object uses "kind" as the first-field discriminator;
// Go has no sum types so each family is modelled as a sealed interface
// with one concrete struct per variant (matching the SignalPresence
// pattern already in use for always-vs-multiplexed signals).
// ---------------------------------------------------------------------------

// DbcNode is a DBC network node (BU_ keyword).
type DbcNode struct {
	Name string
}

// --- Comment targets (CM_ family) ---

// DbcCommentTarget is the sealed sum of the 5 comment-target kinds.
type DbcCommentTarget interface {
	commentTarget() // sealed
}

// DbcCommentTargetNetwork is a network-wide comment.
type DbcCommentTargetNetwork struct{}

func (DbcCommentTargetNetwork) commentTarget() {}

// DbcCommentTargetNode is a node comment.
type DbcCommentTargetNode struct {
	Node string
}

func (DbcCommentTargetNode) commentTarget() {}

// DbcCommentTargetMessage is a message comment. Extended is emitted on
// the wire only when true, matching Agda's formatCANId which omits the
// field for 11-bit standard IDs.
type DbcCommentTargetMessage struct {
	ID       uint32
	Extended bool
}

func (DbcCommentTargetMessage) commentTarget() {}

// DbcCommentTargetSignal is a signal comment.
type DbcCommentTargetSignal struct {
	ID       uint32
	Extended bool
	Signal   string
}

func (DbcCommentTargetSignal) commentTarget() {}

// DbcCommentTargetEnvVar is an environment-variable comment.
type DbcCommentTargetEnvVar struct {
	EnvVar string
}

func (DbcCommentTargetEnvVar) commentTarget() {}

// DbcComment is one CM_ entry with its target and body.
type DbcComment struct {
	Target DbcCommentTarget
	Text   string
}

// --- Attribute scope (BA_DEF_ keyword class) ---

// DbcAttrScope names the scope of a BA_DEF_ attribute declaration.
type DbcAttrScope int

// Attribute scope constants matching Agda AttrScope. The nodeMsg /
// nodeSig entries are the relational scopes introduced by BA_DEF_REL_
// (BU_BO_REL_ / BU_SG_REL_ in DBC text).
const (
	DbcAttrScopeNetwork DbcAttrScope = iota
	DbcAttrScopeNode
	DbcAttrScopeMessage
	DbcAttrScopeSignal
	DbcAttrScopeEnvVar
	DbcAttrScopeNodeMsg
	DbcAttrScopeNodeSig
)

// --- Attribute types (RHS of BA_DEF_) ---

// DbcAttrType is the sealed sum of the 5 attribute-definition kinds.
type DbcAttrType interface {
	attrType() // sealed
}

// DbcAttrTypeInt is an integer attribute definition.
type DbcAttrTypeInt struct {
	Min int64
	Max int64
}

func (DbcAttrTypeInt) attrType() {}

// DbcAttrTypeFloat is a float attribute definition. Bounds use Rational
// to mirror Python's Fraction and preserve ℚ precision end-to-end —
// float64 would drift when a DBC text input carries a non-terminating
// binary fraction.
type DbcAttrTypeFloat struct {
	Min Rational
	Max Rational
}

func (DbcAttrTypeFloat) attrType() {}

// DbcAttrTypeString is a string attribute definition.
type DbcAttrTypeString struct{}

func (DbcAttrTypeString) attrType() {}

// DbcAttrTypeEnum is an enum attribute definition carrying its label set.
type DbcAttrTypeEnum struct {
	Values []string
}

func (DbcAttrTypeEnum) attrType() {}

// DbcAttrTypeHex is a hex attribute definition (unsigned range).
type DbcAttrTypeHex struct {
	Min int64
	Max int64
}

func (DbcAttrTypeHex) attrType() {}

// --- Attribute values (BA_, BA_REL_, BA_DEF_DEF_) ---

// DbcAttrValue is the sealed sum of the 5 attribute-value kinds.
type DbcAttrValue interface {
	attrValue() // sealed
}

// DbcAttrValueInt is an integer attribute value.
type DbcAttrValueInt struct {
	Value int64
}

func (DbcAttrValueInt) attrValue() {}

// DbcAttrValueFloat is a float attribute value. Same Rational-over-double
// rationale as DbcAttrTypeFloat above.
type DbcAttrValueFloat struct {
	Value Rational
}

func (DbcAttrValueFloat) attrValue() {}

// DbcAttrValueString is a string attribute value.
type DbcAttrValueString struct {
	Value string
}

func (DbcAttrValueString) attrValue() {}

// DbcAttrValueEnum is an enum attribute value carrying the ℕ index of
// the chosen label in the corresponding DbcAttrTypeEnum.Values list.
type DbcAttrValueEnum struct {
	Value int64
}

func (DbcAttrValueEnum) attrValue() {}

// DbcAttrValueHex is a hex attribute value.
type DbcAttrValueHex struct {
	Value int64
}

func (DbcAttrValueHex) attrValue() {}

// --- Attribute assignment targets (LHS of BA_ / BA_REL_) ---

// DbcAttrTarget is the sealed sum of the 7 attribute-target kinds.
type DbcAttrTarget interface {
	attrTarget() // sealed
}

// DbcAttrTargetNetwork is a network-scope assignment.
type DbcAttrTargetNetwork struct{}

func (DbcAttrTargetNetwork) attrTarget() {}

// DbcAttrTargetNode is a node-scope assignment.
type DbcAttrTargetNode struct {
	Node string
}

func (DbcAttrTargetNode) attrTarget() {}

// DbcAttrTargetMessage is a message-scope assignment.
type DbcAttrTargetMessage struct {
	ID       uint32
	Extended bool
}

func (DbcAttrTargetMessage) attrTarget() {}

// DbcAttrTargetSignal is a signal-scope assignment.
type DbcAttrTargetSignal struct {
	ID       uint32
	Extended bool
	Signal   string
}

func (DbcAttrTargetSignal) attrTarget() {}

// DbcAttrTargetEnvVar is an env-var-scope assignment.
type DbcAttrTargetEnvVar struct {
	EnvVar string
}

func (DbcAttrTargetEnvVar) attrTarget() {}

// DbcAttrTargetNodeMsg is a node-message relational assignment.
type DbcAttrTargetNodeMsg struct {
	Node     string
	ID       uint32
	Extended bool
}

func (DbcAttrTargetNodeMsg) attrTarget() {}

// DbcAttrTargetNodeSig is a node-signal relational assignment.
type DbcAttrTargetNodeSig struct {
	Node     string
	ID       uint32
	Extended bool
	Signal   string
}

func (DbcAttrTargetNodeSig) attrTarget() {}

// --- Attribute ADT (3 variants: BA_DEF_ / BA_DEF_DEF_ / BA_) ---

// DbcAttribute is the sealed sum of the 3 BA_* entry kinds. Wire
// ordering (definition → default → assignment) is preserved because all
// three variants live in a single flat list.
type DbcAttribute interface {
	attribute() // sealed
}

// DbcAttrDef is an attribute declaration (BA_DEF_ / BA_DEF_REL_).
type DbcAttrDef struct {
	Name     string
	Scope    DbcAttrScope
	AttrType DbcAttrType
}

func (DbcAttrDef) attribute() {}

// DbcAttrDefault is an attribute default (BA_DEF_DEF_ / BA_DEF_DEF_REL_).
type DbcAttrDefault struct {
	Name  string
	Value DbcAttrValue
}

func (DbcAttrDefault) attribute() {}

// DbcAttrAssign is an attribute assignment (BA_ / BA_REL_).
type DbcAttrAssign struct {
	Name   string
	Target DbcAttrTarget
	Value  DbcAttrValue
}

func (DbcAttrAssign) attribute() {}

// ---------------------------------------------------------------------------
// DBC definition and lookup helpers
// ---------------------------------------------------------------------------

// DbcDefinition is a complete DBC database.
//
// Tier 1 metadata slices (SignalGroups / EnvironmentVars / ValueTables)
// mirror the Agda DBC record fields 3-5; Tier 2 slices (Nodes / Comments
// / Attributes) mirror fields 6-8. All six are written on every
// format_dbc response even when empty, matching the C++ and Python
// bindings.
type DbcDefinition struct {
	Version         string
	Messages        []DbcMessage
	SignalGroups    []DbcSignalGroup
	EnvironmentVars []DbcEnvironmentVar
	ValueTables     []DbcValueTable
	Nodes           []DbcNode
	Comments        []DbcComment
	Attributes      []DbcAttribute
	nameIndex       map[string]int // maps message name -> index
	idIndex         map[uint64]int // maps composite CAN ID key -> index
}

// NewDbcDefinition creates a [DbcDefinition] with its message-name and
// CAN-ID lookup indexes populated. External loaders must use this
// constructor — directly populating the struct leaves the indexes nil and
// forces [DbcDefinition.MessageByID] and [DbcDefinition.MessageByName] onto
// their linear fallback paths.
func NewDbcDefinition(version string, messages []DbcMessage) *DbcDefinition {
	d := &DbcDefinition{Version: version, Messages: messages}
	d.buildIndexes()
	return d
}

// buildIndexes populates the message name and ID lookup indexes.
func (d *DbcDefinition) buildIndexes() {
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
func canIDKey(id CanID) uint64 {
	k := uint64(id.Value())
	if id.IsExtended() {
		k |= extendedIDFlag
	}
	return k
}

// MessageByID returns the first message with the given CAN ID, or nil if not found.
// The returned pointer is a deep copy; mutating it does not affect the DbcDefinition.
func (d *DbcDefinition) MessageByID(id CanID) *DbcMessage {
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
// The returned pointer is a deep copy; mutating it does not affect the DbcDefinition.
func (d *DbcDefinition) MessageByName(name MessageName) *DbcMessage {
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

// copyMessage returns a deep copy of a DbcMessage, including its Signals slice.
func copyMessage(m *DbcMessage) *DbcMessage {
	out := *m
	out.Signals = append([]DbcSignal(nil), m.Signals...)
	return &out
}
