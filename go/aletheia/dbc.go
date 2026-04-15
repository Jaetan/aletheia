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
// DBC definition and lookup helpers
// ---------------------------------------------------------------------------

// DbcDefinition is a complete DBC database.
type DbcDefinition struct {
	Version   string
	Messages  []DbcMessage
	nameIndex map[string]int // maps message name -> index
	idIndex   map[uint64]int // maps composite CAN ID key -> index
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
