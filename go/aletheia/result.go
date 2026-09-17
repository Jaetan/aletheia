// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

// SignalValue is one signal and its value, the same type going in to
// [Client.BuildFrame] and coming out of an extraction. The value is exact: the
// wire carries a numerator and a denominator, so a value the kernel computed
// arrives as it was computed. Build one with [IntRational] for a whole number
// or [FromDecimal] for decimal text.
type SignalValue struct {
	Name  SignalName
	Value Rational
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
	index  map[SignalName]Rational // built at construction by buildIndex
}

// buildIndex fills the lookup from the values. Called once at construction.
func (r *ExtractionResult) buildIndex() {
	r.index = make(map[SignalName]Rational, len(r.Values))
	for _, sv := range r.Values {
		r.index[sv.Name] = sv.Value
	}
}

// Get is the value of a signal and whether it was there. The value is the
// exact rational the kernel computed; read its two components to do exact
// arithmetic with it.
func (r *ExtractionResult) Get(name SignalName) (Rational, bool) {
	v, ok := r.index[name]
	return v, ok
}

// FrameResponse is the response to a single frame during streaming.
type FrameResponse interface {
	frameResponse() // sealed
}

// Ack is a frame that produced no property event at all.
type Ack struct{}

func (Ack) frameResponse() {}

// PropertyBatch is a frame that produced at least one property event: the
// properties that came true at this frame, in the order they were declared,
// followed by a violation when one ended the stream. A frame with no events is
// an Ack, so a batch is never empty.
type PropertyBatch struct {
	Results []PropertyResult
}

func (PropertyBatch) frameResponse() {}

// FirstViolation is the violation of the batch, or nothing when the batch
// carries only properties that came true. A batch holds at most one violation,
// which the kernel puts last, so the first is the only.
func (b PropertyBatch) FirstViolation() *PropertyResult {
	for i := range b.Results {
		if b.Results[i].Verdict == Fails {
			return &b.Results[i]
		}
	}
	return nil
}

// Satisfactions are the properties that came true at this frame, none when
// the batch carries only a violation.
func (b PropertyBatch) Satisfactions() []PropertyResult {
	var out []PropertyResult
	for _, r := range b.Results {
		if r.Verdict == Holds {
			out = append(out, r)
		}
	}
	return out
}

// Verdict is what became of a property by the end of the stream.
//
// Unresolved is the third value: the trace neither proved the property nor
// broke it. The usual cause is a predicate over a signal no frame carried, so
// nothing was ever decided about it. It is reported as its own verdict rather
// than as a failure, because the semantics the kernel is proved against says
// the same. The package documentation states the contract under streaming
// adequacy.
type Verdict int

//go:generate stringer -type=Verdict -linecomment -output=verdict_string.go

const (
	// Holds means the property was satisfied.
	Holds Verdict = iota // holds
	// Fails means the property was violated.
	Fails // fails
	// Unresolved means the verdict is Unknown (three-valued Kleene).
	Unresolved // unresolved
)

// PropertyResult is the end-of-stream verdict for a single property.
type PropertyResult struct {
	PropertyIndex PropertyIndex
	Verdict       Verdict
	Timestamp     *Timestamp           // nil if not applicable
	Reason        string               // raw reason from the Agda core; may be empty
	Enrichment    *ViolationEnrichment // nil when verdict is Holds or no diagnostic
}

// StreamWarning is something the kernel noticed while deciding, reported at
// the end of the stream.
//
// The kind uncached_atom says a property asked about a signal no frame
// carried. Its Unresolved verdict is right either way, and without the warning
// a caller cannot tell that case from a property the trace genuinely left
// open. A kind this binding does not know is carried rather than refused, so
// that a kernel adding one does not break a caller.
type StreamWarning struct {
	Kind          string
	PropertyIndex int
	Detail        string
}

// StreamResult is a verdict per property, and the warnings the kernel raised
// along the way, of which there are none when every predicate saw its signal.
type StreamResult struct {
	Results  []PropertyResult
	Warnings []StreamWarning
}

// IssueSeverity classifies a validation issue.
type IssueSeverity int

//go:generate stringer -type=IssueSeverity -linecomment -output=issueseverity_string.go

const (
	// SeverityError indicates a structural issue that prevents correct operation.
	SeverityError IssueSeverity = iota // error
	// SeverityWarning indicates a suspicious but non-fatal issue.
	SeverityWarning // warning
)

// IssueCode identifies a specific type of DBC validation issue.
type IssueCode string

const (
	// IssueDuplicateMessageID is two messages share the same CAN ID.
	IssueDuplicateMessageID IssueCode = "duplicate_message_id"
	// IssueDuplicateMessageName is two messages share the same name.
	IssueDuplicateMessageName IssueCode = "duplicate_message_name"
	// IssueDuplicateSignalName is two signals in the same message share a name.
	IssueDuplicateSignalName IssueCode = "duplicate_signal_name"
	// IssueFactorZero is signal scaling factor is zero (division by zero).
	IssueFactorZero IssueCode = "factor_zero"
	// IssueMultiplexorNotFound is multiplexed signal references a missing multiplexor.
	IssueMultiplexorNotFound IssueCode = "multiplexor_not_found"
	// IssueMultiplexorCycle is multiplexor chain references itself (cycle).
	IssueMultiplexorCycle IssueCode = "multiplexor_cycle"
	// IssueGlobalNameCollision is signal name is not unique across all messages.
	IssueGlobalNameCollision IssueCode = "global_name_collision"
	// IssueMinExceedsMax is signal physical min exceeds max.
	IssueMinExceedsMax IssueCode = "min_exceeds_max"
	// IssueSignalExceedsDLC is signal bit range extends beyond the message DLC.
	IssueSignalExceedsDLC IssueCode = "signal_exceeds_dlc"
	// IssueSignalOverlap is two signals occupy overlapping bit positions.
	IssueSignalOverlap IssueCode = "signal_overlap"
	// IssueBitLengthZero is signal has zero bit length.
	IssueBitLengthZero IssueCode = "bit_length_zero"
	// IssueOffsetScaleRange is offset/scale combination produces out-of-range values.
	IssueOffsetScaleRange IssueCode = "offset_scale_range"
	// IssueEmptyMessage is message declares no signals.
	IssueEmptyMessage IssueCode = "empty_message"
	// IssueStartBitOutOfRange is signal start bit exceeds frame capacity.
	IssueStartBitOutOfRange IssueCode = "start_bit_out_of_range"
	// IssueBitLengthExcessive is signal bit length exceeds the frame capacity.
	IssueBitLengthExcessive IssueCode = "bit_length_excessive"
	// IssueMultiplexorNonUnitScaling is multiplexor signal has non-unit scaling (factor≠1 or offset≠0).
	IssueMultiplexorNonUnitScaling IssueCode = "multiplexor_non_unit_scaling"
	// IssueDuplicateAttributeName is BA_DEF_ declares the same attribute name twice.
	IssueDuplicateAttributeName IssueCode = "duplicate_attribute_name"
	// IssueUnknownCommentTarget is CM_ entry references a node/message/signal/env-var that is not declared.
	IssueUnknownCommentTarget IssueCode = "unknown_comment_target"
	// IssueUnknownMessageSender is message sender node is not listed in BU_.
	IssueUnknownMessageSender IssueCode = "unknown_message_sender"
	// IssueUnknownSignalReceiver is signal receiver node is not listed in BU_.
	IssueUnknownSignalReceiver IssueCode = "unknown_signal_receiver"
	// IssueUnknownValueDescriptionTarget is VAL_ line references (canID, signalName) with no matching signal in any message.
	IssueUnknownValueDescriptionTarget IssueCode = "unknown_value_description_target"
	// IssueTextRoundtripDivergence is FormatDBCText: re-parsing the emitted text does not reproduce the input DBC.
	IssueTextRoundtripDivergence IssueCode = "text_roundtrip_divergence"
	// IssueMultiValueMuxSelector is a mux signal is present for multiple selector values (not expressible in .dbc text).
	IssueMultiValueMuxSelector IssueCode = "multi_value_mux_selector"
	// IssueMuxMasterIncoherent is the mux master signal's presence is inconsistent with its slaves.
	IssueMuxMasterIncoherent IssueCode = "mux_master_incoherent"
	// IssueUnknownAttributeName is a BA_ assignment/default references an attribute with no BA_DEF_ declaration.
	IssueUnknownAttributeName IssueCode = "unknown_attribute_name"
	// IssueAttributeValueTypeMismatch is an attribute value's type does not match its BA_DEF_ declaration.
	IssueAttributeValueTypeMismatch IssueCode = "attribute_value_type_mismatch"
	// IssueAttributeEnumEmpty is an enum attribute (BA_DEF_ ENUM) declares no values.
	IssueAttributeEnumEmpty IssueCode = "attribute_enum_empty"
	// IssueAttributeEnumDefaultUnstable is an enum attribute's default index does not resolve back to itself.
	IssueAttributeEnumDefaultUnstable IssueCode = "attribute_enum_default_unstable"
	// IssueUnknown is unrecognized issue code from the Agda core.
	IssueUnknown IssueCode = "unknown"
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

// ParsedDBC is a definition that parsed and validated: both routes into the
// kernel run the validator, and this is what comes back when it found nothing
// of error severity. Whatever it found besides is here as warnings; an error
// arrives as a refusal instead.
type ParsedDBC struct {
	DBC      DBCDefinition
	Warnings []ValidationIssue
}

// DBCText is a definition written back out as .dbc text, with whatever the
// kernel wants to say about it. The text is only ever returned when the kernel
// has proved it re-parses to the definition it came from, so the issues here
// are advisory; a definition whose text would not re-parse is refused as a
// [TextRoundTripFailedError] instead.
type DBCText struct {
	Text   string
	Issues []ValidationIssue
}
