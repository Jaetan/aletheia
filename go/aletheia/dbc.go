package aletheia

// SignalPresence describes when a signal is present in a frame.
type SignalPresence interface {
	signalPresence() // sealed
}

// AlwaysPresent means the signal is in every frame of its message.
type AlwaysPresent struct{}

func (AlwaysPresent) signalPresence() {}

// Multiplexed means the signal is present only when a multiplexor has a specific value.
type Multiplexed struct {
	Multiplexor SignalName
	MuxValue    MultiplexValue
}

func (Multiplexed) signalPresence() {}

// DbcSignal defines a single signal within a DBC message.
type DbcSignal struct {
	Name      SignalName
	StartBit  BitPosition
	BitLength BitLength
	ByteOrder ByteOrder
	IsSigned  bool
	Factor    ScaleFactor
	Offset    ScaleOffset
	Minimum   PhysicalValue
	Maximum   PhysicalValue
	Unit      Unit
	Presence  SignalPresence
}

// DbcMessage defines a CAN message with its signals.
type DbcMessage struct {
	ID      CanID
	Name    MessageName
	DLC     DLC
	Sender  NodeName
	Signals []DbcSignal
}

// DbcDefinition is a complete DBC database.
type DbcDefinition struct {
	Version  string
	Messages []DbcMessage
}
