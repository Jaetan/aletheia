package aletheia

// SignalValue is a single extracted signal name-value pair.
type SignalValue struct {
	Name  SignalName
	Value PhysicalValue
}

// SignalError is a single signal extraction error.
type SignalError struct {
	Name  SignalName
	Error string
}

// ExtractionResult contains the result of extracting signals from a frame.
// Signals are partitioned into successfully decoded values, extraction errors,
// and absent signals (not present due to multiplexing).
type ExtractionResult struct {
	Values []SignalValue
	Errors []SignalError
	Absent []SignalName
	index  map[SignalName]PhysicalValue // built at construction by buildIndex
}

// buildIndex populates the lookup index from Values. Called once at construction.
func (r *ExtractionResult) buildIndex() {
	r.index = make(map[SignalName]PhysicalValue, len(r.Values))
	for _, sv := range r.Values {
		r.index[sv.Name] = sv.Value
	}
}

// Get looks up a signal by name, returning its value and true if found.
// Returns (0, false) if the signal is not present or the index was not built.
func (r *ExtractionResult) Get(name SignalName) (PhysicalValue, bool) {
	v, ok := r.index[name]
	return v, ok
}

// FrameResponse is the response to a single frame during streaming.
type FrameResponse interface {
	frameResponse() // sealed
}

// Ack indicates the frame was processed with no property violation.
type Ack struct{}

func (Ack) frameResponse() {}

// Violation indicates a property was violated by this frame.
type Violation struct {
	PropertyIndex PropertyIndex
	Timestamp     Timestamp
	Reason        string               // raw reason from the Agda core; may be empty
	Enrichment    *ViolationEnrichment // nil when no diagnostic available
}

func (Violation) frameResponse() {}

// Verdict is the final determination for a property at end-of-stream.
//
// Unresolved corresponds to the Agda coalgebra's three-valued Kleene
// "Unsure" verdict: the property was neither proved to hold nor proved to
// fail on the observed trace. The typical cause is an atomic predicate
// whose signal was never observed (e.g. Always(p) where no frame carrying
// p's signal arrived before end-of-stream). The denotational semantics
// agrees this is Unknown, so it is reported as a distinct verdict rather
// than collapsed to Fails.
type Verdict int

const (
	// Holds means the property was satisfied.
	Holds Verdict = iota
	// Fails means the property was violated.
	Fails
	// Unresolved means the verdict is Unknown (three-valued Kleene).
	Unresolved
)

// String returns "holds", "fails", "unresolved", or "unknown".
func (v Verdict) String() string {
	switch v {
	case Holds:
		return "holds"
	case Fails:
		return "fails"
	case Unresolved:
		return "unresolved"
	default:
		return "unknown"
	}
}

// PropertyResult is the end-of-stream verdict for a single property.
type PropertyResult struct {
	PropertyIndex PropertyIndex
	Verdict       Verdict
	Timestamp     *Timestamp           // nil if not applicable
	Reason        string               // raw reason from the Agda core; may be empty
	Enrichment    *ViolationEnrichment // nil when verdict is Holds or no diagnostic
}

// StreamResult contains the end-of-stream verdicts for all properties.
type StreamResult struct {
	Results []PropertyResult
}

// IssueSeverity classifies a validation issue.
type IssueSeverity int

const (
	// SeverityError indicates a structural issue that prevents correct operation.
	SeverityError IssueSeverity = iota
	// SeverityWarning indicates a suspicious but non-fatal issue.
	SeverityWarning
)

// String returns "error", "warning", or "unknown".
func (s IssueSeverity) String() string {
	switch s {
	case SeverityError:
		return "error"
	case SeverityWarning:
		return "warning"
	default:
		return "unknown"
	}
}

// IssueCode identifies a specific type of DBC validation issue.
type IssueCode string

const (
	IssueDuplicateMessageID        IssueCode = "duplicate_message_id"         // Two messages share the same CAN ID.
	IssueDuplicateMessageName      IssueCode = "duplicate_message_name"       // Two messages share the same name.
	IssueDuplicateSignalName       IssueCode = "duplicate_signal_name"        // Two signals in the same message share a name.
	IssueFactorZero                IssueCode = "factor_zero"                  // Signal scaling factor is zero (division by zero).
	IssueMultiplexorNotFound       IssueCode = "multiplexor_not_found"        // Multiplexed signal references a missing multiplexor.
	IssueMultiplexorCycle          IssueCode = "multiplexor_cycle"            // Multiplexor chain references itself (cycle).
	IssueGlobalNameCollision       IssueCode = "global_name_collision"        // Signal name is not unique across all messages.
	IssueMinExceedsMax             IssueCode = "min_exceeds_max"              // Signal physical min exceeds max.
	IssueSignalExceedsDLC          IssueCode = "signal_exceeds_dlc"           // Signal bit range extends beyond the message DLC.
	IssueSignalOverlap             IssueCode = "signal_overlap"               // Two signals occupy overlapping bit positions.
	IssueBitLengthZero             IssueCode = "bit_length_zero"              // Signal has zero bit length.
	IssueOffsetScaleRange          IssueCode = "offset_scale_range"           // Offset/scale combination produces out-of-range values.
	IssueEmptyMessage              IssueCode = "empty_message"                // Message declares no signals.
	IssueStartBitOutOfRange        IssueCode = "start_bit_out_of_range"       // Signal start bit exceeds frame capacity.
	IssueBitLengthExcessive        IssueCode = "bit_length_excessive"         // Signal bit length exceeds 64 bits.
	IssueMultiplexorNonUnitScaling IssueCode = "multiplexor_non_unit_scaling" // Multiplexor signal has non-unit scaling (factor≠1 or offset≠0).
	IssueUnknown                   IssueCode = "unknown"                      // Unrecognized issue code from the Agda core.
)

// ValidationIssue is a single issue found during DBC validation.
type ValidationIssue struct {
	Severity IssueSeverity
	Code     IssueCode
	Detail   string
}

// ValidationResult contains the results of DBC validation.
type ValidationResult struct {
	HasErrors bool
	Issues    []ValidationIssue
}
