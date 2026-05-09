package aletheia

// Adversarial-input bounds — Go mirror of `Aletheia.Limits` (Agda).
//
// Single source of truth: src/Aletheia/Limits.agda; numeric values are
// mirrored here verbatim.  Wire spec: docs/architecture/PROTOCOL.md § Limits.
//
// The Aletheia Agda kernel enforces these bounds at every parser entry; this
// file additionally rejects oversize inputs at the cgo boundary so a
// pathological 100 MiB JSON payload is not marshaled into a C buffer only
// to be rejected on the other side.
//
// Per AGENTS.md universal rule "Adversarial-input bounds at parser surfaces",
// rejection over a bound is a typed *InputBoundExceededError carrying the
// offending kind, the observed value, and the limit it crossed.

// BoundKind* constants identify which bound was exceeded.  Wire codes mirror
// boundKindCode in Aletheia.Limits (Agda).
const (
	BoundKindInputLengthBytes = "input_length_bytes"
	BoundKindNestingDepth     = "nesting_depth"
	BoundKindArrayCardinality = "array_cardinality"
	BoundKindIdentifierLength = "identifier_length"
	BoundKindStringLength     = "string_length"
	BoundKindAtomCount        = "atom_count"
	BoundKindFrameByteCount   = "frame_byte_count"
)

// Numeric bound constants — mirror src/Aletheia/Limits.agda exactly.
const (
	// MaxDBCTextBytes — total DBC-text input length in bytes (64 MiB).
	MaxDBCTextBytes = 64 * 1024 * 1024

	// MaxJSONBytes — total JSON input length in bytes at the FFI boundary (64 MiB).
	MaxJSONBytes = 64 * 1024 * 1024

	// MaxNestingDepth — JSON object/array nesting depth.
	MaxNestingDepth = 64

	// MaxMessagesPerFile — DBC messages per file.
	MaxMessagesPerFile = 10000

	// MaxSignalsPerMessage — signals per single DBC message.
	MaxSignalsPerMessage = 1024

	// MaxAttributesPerFile — attribute definitions / assignments per DBC file.
	MaxAttributesPerFile = 10000

	// MaxValueDescriptionsPerFile — VAL_/VAL_TABLE_ entries per DBC file.
	MaxValueDescriptionsPerFile = 1000000

	// MaxIdentifierLength — DBC identifier length in characters.
	MaxIdentifierLength = 128

	// MaxStringLengthBytes — quoted-string body length in bytes (64 KiB).
	MaxStringLengthBytes = 64 * 1024

	// MaxAtomCountPerProperty — LTL atoms per single property.
	MaxAtomCountPerProperty = 1024

	// MaxFrameByteCount — CAN frame payload byte count (CAN-FD maximum).
	MaxFrameByteCount = 64
)
