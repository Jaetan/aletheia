// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

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

// Ack indicates the frame was processed with no property events at all
// (no halt, no completion).
type Ack struct{}

func (Ack) frameResponse() {}

// PropertyBatch is the response to a frame that produced one or more
// property events: mid-stream Satisfactions (properties that completed
// at this frame) followed by an optional terminal Violation, in
// source-order per the Agda dispatchIterResult invariant.  R23 —
// AGDA-D-12.1: pre-R23 only single Violation frames were surfaced; the
// silent drop of mid-stream Satisfactions has been lifted to the wire.
//
// Empty Results is unreachable — frames with no events return Ack.
type PropertyBatch struct {
	Results []PropertyResult
}

func (PropertyBatch) frameResponse() {}

// FirstViolation returns the first PropertyResult with Verdict == Fails,
// or nil if the batch carries only mid-stream Satisfactions.  Per the
// Agda invariant, a batch contains at most one violation and (if
// present) it is the last entry, so this is also "the violation".
func (b PropertyBatch) FirstViolation() *PropertyResult {
	for i := range b.Results {
		if b.Results[i].Verdict == Fails {
			return &b.Results[i]
		}
	}
	return nil
}

// Satisfactions returns the mid-stream Satisfaction entries (Verdict ==
// Holds).  Empty when the batch is violation-only or unresolved-only.
func (b PropertyBatch) Satisfactions() []PropertyResult {
	var out []PropertyResult
	for _, r := range b.Results {
		if r.Verdict == Holds {
			out = append(out, r)
		}
	}
	return out
}

// Verdict is the final determination for a property at end-of-stream.
//
// Unresolved corresponds to the Agda coalgebra's three-valued Kleene
// "Unsure" verdict: the property was neither proved to hold nor proved to
// fail on the observed trace. The typical cause is an atomic predicate
// whose signal was never observed (e.g. Always(p) where no frame carrying
// p's signal arrived before end-of-stream). This is the user-observable
// manifestation of a violated AllObserved invariant — see the package
// doc § "Streaming adequacy" for the full contract. The denotational
// semantics agrees this is Unknown, so it is reported as a distinct
// verdict rather than collapsed to Fails.
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

// StreamWarning is one diagnostic surfaced by the kernel at EndStream.
//
// R21 cluster 1 — AGDA-D-12.1: Kind == "uncached_atom" is emitted when a
// property's atom references a signal that never appeared in trace.  The
// Unresolved verdict on that property is sound (three-valued Kleene
// Unknown) but indistinguishable from a genuine Kleene-undecidable
// Unresolved without this warning.
//
// New kinds are additive on the wire (the kernel adds new WarningKind
// constructors; bindings should accept unknown Kind values rather than
// rejecting them).
type StreamWarning struct {
	Kind          string
	PropertyIndex int
	Detail        string
}

// StreamResult contains the end-of-stream verdicts for all properties
// plus any cache-miss diagnostic warnings (empty when every atom's
// signal was observed at least once).
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
	// IssueDuplicateMessageID — two messages share the same CAN ID.
	IssueDuplicateMessageID IssueCode = "duplicate_message_id"
	// IssueDuplicateMessageName — two messages share the same name.
	IssueDuplicateMessageName IssueCode = "duplicate_message_name"
	// IssueDuplicateSignalName — two signals in the same message share a name.
	IssueDuplicateSignalName IssueCode = "duplicate_signal_name"
	// IssueFactorZero — signal scaling factor is zero (division by zero).
	IssueFactorZero IssueCode = "factor_zero"
	// IssueMultiplexorNotFound — multiplexed signal references a missing multiplexor.
	IssueMultiplexorNotFound IssueCode = "multiplexor_not_found"
	// IssueMultiplexorCycle — multiplexor chain references itself (cycle).
	IssueMultiplexorCycle IssueCode = "multiplexor_cycle"
	// IssueGlobalNameCollision — signal name is not unique across all messages.
	IssueGlobalNameCollision IssueCode = "global_name_collision"
	// IssueMinExceedsMax — signal physical min exceeds max.
	IssueMinExceedsMax IssueCode = "min_exceeds_max"
	// IssueSignalExceedsDLC — signal bit range extends beyond the message DLC.
	IssueSignalExceedsDLC IssueCode = "signal_exceeds_dlc"
	// IssueSignalOverlap — two signals occupy overlapping bit positions.
	IssueSignalOverlap IssueCode = "signal_overlap"
	// IssueBitLengthZero — signal has zero bit length.
	IssueBitLengthZero IssueCode = "bit_length_zero"
	// IssueOffsetScaleRange — offset/scale combination produces out-of-range values.
	IssueOffsetScaleRange IssueCode = "offset_scale_range"
	// IssueEmptyMessage — message declares no signals.
	IssueEmptyMessage IssueCode = "empty_message"
	// IssueStartBitOutOfRange — signal start bit exceeds frame capacity.
	IssueStartBitOutOfRange IssueCode = "start_bit_out_of_range"
	// IssueBitLengthExcessive — signal bit length exceeds 64 bits.
	IssueBitLengthExcessive IssueCode = "bit_length_excessive"
	// IssueMultiplexorNonUnitScaling — multiplexor signal has non-unit scaling (factor≠1 or offset≠0).
	IssueMultiplexorNonUnitScaling IssueCode = "multiplexor_non_unit_scaling"
	// IssueDuplicateAttributeName — BA_DEF_ declares the same attribute name twice.
	IssueDuplicateAttributeName IssueCode = "duplicate_attribute_name"
	// IssueUnknownCommentTarget — CM_ entry references a node/message/signal/env-var that is not declared.
	IssueUnknownCommentTarget IssueCode = "unknown_comment_target"
	// IssueUnknownMessageSender — message sender node is not listed in BU_.
	IssueUnknownMessageSender IssueCode = "unknown_message_sender"
	// IssueUnknownSignalReceiver — signal receiver node is not listed in BU_.
	IssueUnknownSignalReceiver IssueCode = "unknown_signal_receiver"
	// IssueUnknownValueDescriptionTarget — VAL_ line references (canID, signalName) with no matching signal in any message.
	IssueUnknownValueDescriptionTarget IssueCode = "unknown_value_description_target"
	// IssueUnknown — unrecognized issue code from the Agda core.
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

// ParsedDBC is the success-path result of ParseDBC and ParseDBCText.
//
// Both paths run the structural validator alongside the parser; if the
// parsed DBC has zero error-severity issues, the Agda core emits this
// shape carrying the canonical body plus any non-error issues
// (warnings).  Errors short-circuit to the (*ParsedDBC, error) tuple's
// error half.
type ParsedDBC struct {
	DBC      DBCDefinition
	Warnings []ValidationIssue
}
