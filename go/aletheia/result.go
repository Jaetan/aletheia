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
}

// Get looks up a signal by name, returning its value and true if found.
func (r *ExtractionResult) Get(name SignalName) (PhysicalValue, bool) {
	for _, sv := range r.Values {
		if sv.Name == name {
			return sv.Value, true
		}
	}
	return 0, false
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
	Reason        string // may be empty
}

func (Violation) frameResponse() {}

// Verdict is the final determination for a property.
type Verdict int

const (
	// Holds means the property was satisfied.
	Holds Verdict = iota
	// Fails means the property was violated.
	Fails
)

func (v Verdict) String() string {
	switch v {
	case Holds:
		return "holds"
	case Fails:
		return "fails"
	default:
		return "unknown"
	}
}

// PropertyResult is the end-of-stream verdict for a single property.
type PropertyResult struct {
	PropertyIndex PropertyIndex
	Verdict       Verdict
	Timestamp     *Timestamp // nil if not applicable
	Reason        string     // may be empty
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

// IssueCode identifies a specific type of DBC validation issue.
type IssueCode string

const (
	IssueDuplicateMessageID          IssueCode = "duplicate_message_id"
	IssueDuplicateMessageName        IssueCode = "duplicate_message_name"
	IssueDuplicateSignalName         IssueCode = "duplicate_signal_name"
	IssueFactorZero                  IssueCode = "factor_zero"
	IssueMultiplexorNotFound         IssueCode = "multiplexor_not_found"
	IssueMultiplexorNotAlwaysPresent IssueCode = "multiplexor_not_always_present"
	IssueGlobalNameCollision         IssueCode = "global_name_collision"
	IssueMinExceedsMax               IssueCode = "min_exceeds_max"
	IssueSignalExceedsDLC            IssueCode = "signal_exceeds_dlc"
	IssueSignalOverlap               IssueCode = "signal_overlap"
	IssueBitLengthZero               IssueCode = "bit_length_zero"
	IssueDLCOutOfRange               IssueCode = "dlc_out_of_range"
	IssueOffsetScaleRange            IssueCode = "offset_scale_range"
	IssueEmptyMessage                IssueCode = "empty_message"
	IssueStartBitOutOfRange          IssueCode = "start_bit_out_of_range"
	IssueBitLengthExcessive          IssueCode = "bit_length_excessive"
	IssueUnknown                     IssueCode = "unknown"
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
