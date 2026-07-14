// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"cmp"
	"context"
	"errors"
	"fmt"
	"io"
	"iter"
	"log/slog"
	"slices"
	"sync"
	"sync/atomic"
	"unsafe"
)

// Compile-time assertion: Client implements io.Closer.
var _ io.Closer = (*Client)(nil)

// ClientOption configures optional [Client] behavior.
type ClientOption func(*Client)

// WithLogger sets a structured logger for operational events.
// When nil (default), no logging occurs and there is zero overhead.
func WithLogger(l *slog.Logger) ClientOption {
	return func(c *Client) { c.logger = l }
}

// WithDefaultChecks sets checks that are prepended to every AddChecks call.
func WithDefaultChecks(checks ...CheckResult) ClientOption {
	return func(c *Client) { c.defaultChecks = checks }
}

// Client provides Aletheia operations over a Backend.
//
// A Client is safe for concurrent use from multiple goroutines; calls are
// serialized internally because the underlying LTL automaton is sequential.
// The serializing primitive is a 1-deep channel-based semaphore — a goroutine
// waiting for the lock may be cancelled by its [context.Context] without ever
// acquiring the lock, a behavior [sync.Mutex] cannot express. Every operation
// method takes a [context.Context] as its first parameter; see
// docs/architecture/CANCELLATION.md for the cancellation contract.
//
// Create with [NewClient] and close with [Client.Close] (implements [io.Closer]).
// The lockCh + closeOnce pair may look like inconsistent sync primitives but
// intentionally solve different problems:
//   - lockCh is a 1-deep channel semaphore.  Its purpose is context-aware
//     mutual exclusion — every Client method's lock() helper does
//     `select { case lockCh <- struct{}{}: ... case <-ctx.Done(): ... }`
//     so callers can cancel a blocked acquisition.  sync.Mutex.Lock has no
//     context-cancellable variant; TryLock returns immediately and doesn't
//     wait.  This is a hard requirement per docs/architecture/CANCELLATION.md.
//   - closeOnce is sync.Once for one-shot Close().  Double-close safety is
//     a library guarantee; sync.Once is the idiomatic primitive (clearer
//     than a CAS on `closed`).
//
// Consolidating to either primitive alone would lose a capability.
// Revisit only if Go stdlib gains a unified context-aware-mutex-with-
// idempotent-close primitive.
type Client struct {
	backend       Backend
	state         unsafe.Pointer
	lockCh        chan struct{} // 1-deep semaphore: empty=unlocked, full=locked
	closeOnce     sync.Once
	closed        bool
	logger        *slog.Logger              // nil = no logging
	defaultChecks []CheckResult             // prepended by AddChecks
	diags         []PropertyDiagnostic      // one per property, auto-derived
	cache         *extractCache             // extraction cache for enrichment
	lastFrames    map[uint64]lastFrameData  // last frame seen per CAN ID, for EOS enrichment
	signalIndex   map[uint64]map[string]int // signal name -> 0-based index, keyed by (canId, extended)
	signalNames   map[uint64][]string       // index -> signal name, keyed by (canId, extended)
	// lockWaiters counts goroutines currently inside [Client.lock]
	// (between the entry Add(1) and the deferred Add(-1)).  Test-only
	// observability: lets cancel-while-waiting tests deterministically
	// detect that a competing goroutine has reached the lock-acquisition
	// select without falling back to time.Sleep — see cancel_test.go.
	lockWaiters atomic.Int32
}

// NewClient creates a Client backed by the given Backend.
// It calls backend.Init() to create a session.
//
// NewClient does NOT take a [context.Context]: construction is synchronous
// (CGO + GHC RTS init); there is no I/O to wait on, so cancellation has no
// meaningful effect. Mirrors sql.Open / grpc.NewClient. See
// docs/architecture/CANCELLATION.md §5.1.
func NewClient(backend Backend, opts ...ClientOption) (*Client, error) {
	state, err := backend.Init()
	if err != nil {
		return nil, err
	}
	c := &Client{
		backend: backend,
		state:   state,
		lockCh:  make(chan struct{}, 1),
	}
	for _, opt := range opts {
		opt(c)
	}
	return c, nil
}

// Close finalizes the session. The Client must not be used after Close.
// Close is safe to call concurrently or multiple times.
//
// Close does NOT take a [context.Context]: teardown is best-effort,
// idempotent, and double-close safe — matches db.Close / resp.Body.Close
// precedent. If an FFI call is in flight, Close blocks until it returns;
// cancellation cannot preempt the GHC RTS. See CANCELLATION.md §5.1.
func (c *Client) Close() error {
	c.closeOnce.Do(func() {
		// Bare-channel acquire (no ctx). Blocks until any in-flight FFI
		// call returns its lock; cooperative cleanup, not preemptive.
		c.lockCh <- struct{}{}
		defer func() { <-c.lockCh }()
		if c.state != nil {
			c.backend.Close(c.state)
			c.state = nil
			c.closed = true
		}
	})
	return nil
}

// lock acquires the client lock with ctx-aware cancellation. Returns
// ctx.Err() if ctx is already cancelled or fires while waiting on the
// lock, in which case the lock is NOT held and the caller must NOT
// call unlock. Cooperative-at-FFI-boundaries per CANCELLATION.md §1.1.
//
// lockWaiters is incremented on entry and decremented on return so
// tests can observe when a goroutine has reached the select without
// polling on time.Sleep — see cancel_test.go.
func (c *Client) lock(ctx context.Context) error {
	c.lockWaiters.Add(1)
	defer c.lockWaiters.Add(-1)
	select {
	case <-ctx.Done():
		return ctx.Err()
	case c.lockCh <- struct{}{}:
		return nil
	}
}

// unlock releases the client lock. Caller must have successfully called
// lock first.
func (c *Client) unlock() {
	<-c.lockCh
}

// acquire combines [Client.lock] + post-lock context recheck into a
// single helper.  Returns a release closure the caller defers; the
// release is a no-op when err is non-nil (lock was either never held
// or already released by acquire before returning).
//
// Behavior matches the previous open-coded `c.lock(ctx); defer
// c.unlock(); ctx.Err()` triple — including the TOCTOU-tightening
// recheck that catches ctx cancellation between lock acquisition and
// the next FFI call.  The name parameter is the public method name
// used for error-wrap prefixing.
func (c *Client) acquire(ctx context.Context, name string) (release func(), err error) {
	if err := c.lock(ctx); err != nil {
		return nil, fmt.Errorf("%s: %w", name, err)
	}
	if err := ctx.Err(); err != nil {
		c.unlock()
		return nil, fmt.Errorf("%s: %w", name, err)
	}
	return c.unlock, nil
}

// IsClosed reports whether [Client.Close] has been called.  Acquires
// the same internal lock as the data-path operations so the answer
// reflects committed state (no torn reads).  Cross-binding parity
// with Python's “AletheiaClient.is_closed“ property.
func (c *Client) IsClosed() bool {
	c.lockCh <- struct{}{}
	defer func() { <-c.lockCh }()
	return c.closed
}

// processLocked sends input to the backend. Caller must hold the client lock.
func (c *Client) processLocked(input string) (string, error) {
	if c.closed {
		return "", stateError("client is closed")
	}
	return c.backend.Process(c.state, input)
}

// lastFrameData stores the last frame seen for a CAN ID, for EOS enrichment.
type lastFrameData struct {
	id   CANID
	dlc  DLC
	data FramePayload
}

// validatePayload checks that the payload length matches the DLC byte count.
func validatePayload(dlc DLC, data FramePayload) error {
	expected := dlc.ToBytes()
	if len(data) != expected {
		return validationError(fmt.Sprintf("payload length %d does not match DLC %d (expected %d bytes)", len(data), dlc.Value(), expected))
	}
	return nil
}

// resolveSignalIndices looks up signal names in the cached index and converts values to rationals.
// Returns parallel arrays of (indices, numerators, denominators).
func (c *Client) resolveSignalIndices(signals []SignalValue, id CANID, cmdName string) ([]uint32, []int64, []int64, error) {
	if c.signalIndex == nil {
		return nil, nil, nil, stateError(cmdName + ": no DBC loaded (call ParseDBC first)")
	}
	key := canIDKey(id)
	indexMap, ok := c.signalIndex[key]
	if !ok {
		return nil, nil, nil, validationError(fmt.Sprintf("%s: no DBC message for CAN ID %d (extended=%v)", cmdName, id.Value(), id.IsExtended()))
	}
	indices := make([]uint32, 0, len(signals))
	nums := make([]int64, 0, len(signals))
	dens := make([]int64, 0, len(signals))
	for _, sv := range signals {
		idx, found := indexMap[string(sv.Name)]
		if !found {
			return nil, nil, nil, validationError(fmt.Sprintf("%s: unknown signal %q for CAN ID %d", cmdName, sv.Name, id.Value()))
		}
		// SignalValue.Value is an exact Rational (build via IntRational or the
		// kernel FromDecimal). Validate the denominator the wire requires; a
		// Rational has no NaN/Inf, so only the denominator needs checking.
		if err := validateRational(fmt.Sprintf("%s: signal %q", cmdName, sv.Name), sv.Value); err != nil {
			return nil, nil, nil, err
		}
		indices = append(indices, uint32(idx))
		nums = append(nums, sv.Value.Numerator)
		dens = append(dens, sv.Value.Denominator)
	}
	return indices, nums, dens, nil
}

// --- DBC operations ---

// populateSignalLookup rebuilds the name-to-index lookup from a parsed DBC.
// Both ParseDBC and ParseDBCText call this after the Agda core returns
// a validated body so subsequent BuildFrame/UpdateFrame calls can resolve
// signal names against the canonical (post-validation) DBC.
func (c *Client) populateSignalLookup(dbc DBCDefinition) {
	c.signalIndex = make(map[uint64]map[string]int, len(dbc.Messages))
	c.signalNames = make(map[uint64][]string, len(dbc.Messages))
	for _, msg := range dbc.Messages {
		key := canIDKey(msg.ID)
		sigMap := make(map[string]int, len(msg.Signals))
		names := make([]string, len(msg.Signals))
		for i, sig := range msg.Signals {
			sigMap[string(sig.Name)] = i
			names[i] = string(sig.Name)
		}
		c.signalIndex[key] = sigMap
		c.signalNames[key] = names
	}
}

// ParseDBC sends a DBC definition to the Agda core for parsing and loading.
// Subsequent signal extraction and frame building use this parsed definition.
// Returns the parsed body plus any non-error validation issues (warnings);
// validation errors short-circuit to the error half of the tuple.
// Populates the signal name-to-index cache for BuildFrame/UpdateFrame.
//
// Honors ctx cancellation: if ctx is cancelled before lock acquisition (or
// while waiting), returns the wrapped ctx.Err() without making the FFI call.
// If ctx fires during an in-flight FFI call, the call runs to completion and
// returns its real result; the next call fails fast.
func (c *Client) ParseDBC(ctx context.Context, dbc DBCDefinition) (*ParsedDBC, error) {
	dbcJSON, err := serializeDBC(dbc)
	if err != nil {
		return nil, err
	}
	cmd, err := serializeCommand("parseDBC", map[string]any{
		"dbc": dbcJSON,
	})
	if err != nil {
		return nil, err
	}
	release, err := c.acquire(ctx, "ParseDBC")
	if err != nil {
		return nil, err
	}
	defer release()
	resp, err := c.processLocked(cmd)
	if err != nil {
		return nil, err
	}
	parsed, err := parseParsedDBCResponse(resp)
	if err != nil {
		return nil, err
	}
	c.populateSignalLookup(parsed.DBC)
	if c.logger != nil {
		c.logger.LogAttrs(ctx, slog.LevelInfo, "dbc.parsed",
			slog.Int("messages", len(parsed.DBC.Messages)),
			slog.Int("warnings", len(parsed.Warnings)))
	}
	return parsed, nil
}

// ParseDBCText sends raw DBC source text to the Agda core's verified text
// parser, which validates the parse and returns a typed body plus any
// non-error issues (warnings).  Mirrors ParseDBC's success-path shape.
// Populates the signal name-to-index cache for BuildFrame/UpdateFrame.
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) ParseDBCText(ctx context.Context, text string) (*ParsedDBC, error) {
	// Defense-in-depth for cross-binding parity:
	// reject DBC text inputs longer than MaxDBCTextBytes before wrapping
	// them in a JSON command.  The outer MaxJSONBytes cap in processLocked
	// covers the wrapped command separately; the additional inner cap
	// matches the Agda kernel's two-layer enforcement in handleParseDBCText.
	if uint64(len(text)) > MaxDBCTextBytes {
		return nil, newInputBoundExceededError(
			BoundKindInputLengthBytes,
			uint64(len(text)),
			MaxDBCTextBytes,
			CodeInputBoundExceeded,
		)
	}
	cmd, err := serializeCommand("parseDBCText", map[string]any{
		"text": text,
	})
	if err != nil {
		return nil, err
	}
	release, err := c.acquire(ctx, "ParseDBCText")
	if err != nil {
		return nil, err
	}
	defer release()
	resp, err := c.processLocked(cmd)
	if err != nil {
		return nil, err
	}
	parsed, err := parseParsedDBCResponse(resp)
	if err != nil {
		return nil, err
	}
	c.populateSignalLookup(parsed.DBC)
	if c.logger != nil {
		c.logger.LogAttrs(ctx, slog.LevelInfo, "dbc.parsed",
			slog.Int("messages", len(parsed.DBC.Messages)),
			slog.Int("warnings", len(parsed.Warnings)))
	}
	return parsed, nil
}

// ValidateDBC checks a DBC definition for structural issues (overlapping signals,
// factor-zero, DLC violations, etc.) and returns all found issues.
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) ValidateDBC(ctx context.Context, dbc DBCDefinition) (*ValidationResult, error) {
	dbcJSON, err := serializeDBC(dbc)
	if err != nil {
		return nil, err
	}
	cmd, err := serializeCommand("validateDBC", map[string]any{
		"dbc": dbcJSON,
	})
	if err != nil {
		return nil, err
	}
	release, err := c.acquire(ctx, "ValidateDBC")
	if err != nil {
		return nil, err
	}
	defer release()
	resp, err := c.processLocked(cmd)
	if err != nil {
		return nil, err
	}
	return parseValidationResponse(resp)
}

// DEFERRED — TRACKED.
// FormatDBC / FormatDBCText return-type rework (originally a String →
// structured-result migration carrying e.g. rendering options) is deferred.
//
// Why: Structured-result wrapping changes the wire contract across all 3
// bindings; benefits proper typing but unclear payoff vs migration cost.
//
// Revisit when: A consumer needs richer return metadata (e.g. structured
// rendering options) — the migration becomes load-bearing then.
//
// FormatDBC returns the currently loaded DBC definition as parsed by the Agda core.
// Call ParseDBC first.
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) FormatDBC(ctx context.Context) (*DBCDefinition, error) {
	release, err := c.acquire(ctx, "FormatDBC")
	if err != nil {
		return nil, err
	}
	defer release()
	if c.closed {
		return nil, stateError("client is closed")
	}
	resp, err := c.backend.FormatDBCBinary(c.state)
	if err != nil {
		return nil, err
	}
	return parseDBCResponse(resp)
}

// FormatDBCText renders a DBCDefinition as .dbc file text via the verified Agda
// formatter, returning the text image plus its wfTextIssues diagnostics
// (warning-severity, advisory).  Always strict: it returns a [DBCText] only when
// the emitted text provably re-parses to the input DBC — ParseDBCText(
// FormatDBCText(d).Text) returns d byte-identical (a stricter condition than
// validating clean — see the "well-formed DBC" entry in docs/GLOSSARY.md).  A
// DBC whose text does not round-trip is refused with a typed
// [TextRoundTripFailedError] rather than lossy text.  Does not modify client
// state — pass any DBCDefinition value (typically from ParseDBCText, FormatDBC,
// or a JSON load).
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) FormatDBCText(ctx context.Context, dbc DBCDefinition) (*DBCText, error) {
	dbcJSON, err := serializeDBC(dbc)
	if err != nil {
		return nil, err
	}
	cmd, err := serializeCommand("formatDBCText", map[string]any{
		"dbc": dbcJSON,
	})
	if err != nil {
		return nil, err
	}
	release, err := c.acquire(ctx, "FormatDBCText")
	if err != nil {
		return nil, err
	}
	defer release()
	resp, err := c.processLocked(cmd)
	if err != nil {
		return nil, err
	}
	return parseDBCTextResponse(resp)
}

// --- Signal operations ---

// ExtractSignals decodes all signals from a CAN frame using the loaded DBC.
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) ExtractSignals(ctx context.Context, id CANID, dlc DLC, data FramePayload) (*ExtractionResult, error) {
	if err := validatePayload(dlc, data); err != nil {
		return nil, err
	}
	release, err := c.acquire(ctx, "ExtractSignals")
	if err != nil {
		return nil, err
	}
	defer release()
	if c.closed {
		return nil, stateError("client is closed")
	}

	// Use binary path when signal name cache is populated. Only
	// ErrBinaryPathUnsupported (e.g. MockBackend) triggers the JSON
	// fallback — any other error (decode / truncation / real FFI
	// failure) propagates, matching Python's commit-to-binary contract.
	key := canIDKey(id)
	if names, ok := c.signalNames[key]; ok {
		buf, err := c.backend.ExtractSignalsBin(c.state, id, dlc, []byte(data))
		if err == nil {
			return parseExtractionBin(buf, names)
		}
		if !errors.Is(err, ErrBinaryPathUnsupported) {
			return nil, err
		}
	}

	// Fallback: JSON path.
	resp, err := c.backend.ExtractSignalsBinary(c.state, id, dlc, []byte(data))
	if err != nil {
		return nil, err
	}
	return parseExtractionResponse(resp)
}

// BuildFrame encodes signal values into a CAN frame payload.
// Requires a prior ParseDBC call to populate the signal index.
//
// The argument order (id, dlc, signals) matches UpdateFrame and the Python /
// C++ bindings' build_frame(id, dlc, signals) — see CHANGELOG 2.0.0.
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) BuildFrame(ctx context.Context, id CANID, dlc DLC, signals []SignalValue) (FramePayload, error) {
	release, err := c.acquire(ctx, "BuildFrame")
	if err != nil {
		return nil, err
	}
	defer release()
	if c.closed {
		return nil, stateError("client is closed")
	}
	indices, nums, dens, err := c.resolveSignalIndices(signals, id, "BuildFrame")
	if err != nil {
		return nil, err
	}
	payload, err := c.backend.BuildFrameBin(c.state, id, dlc, uint32(len(signals)), indices, nums, dens)
	if err != nil {
		return nil, err
	}
	return FramePayload(payload), nil
}

// UpdateFrame modifies specific signals in an existing CAN frame.
// Requires a prior ParseDBC call to populate the signal index.
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) UpdateFrame(ctx context.Context, id CANID, dlc DLC, data FramePayload, signals []SignalValue) (FramePayload, error) {
	if err := validatePayload(dlc, data); err != nil {
		return nil, err
	}
	release, err := c.acquire(ctx, "UpdateFrame")
	if err != nil {
		return nil, err
	}
	defer release()
	if c.closed {
		return nil, stateError("client is closed")
	}
	indices, nums, dens, err := c.resolveSignalIndices(signals, id, "UpdateFrame")
	if err != nil {
		return nil, err
	}
	payload, err := c.backend.UpdateFrameBin(c.state, id, dlc, []byte(data), uint32(len(signals)), indices, nums, dens)
	if err != nil {
		return nil, err
	}
	return FramePayload(payload), nil
}

// --- Streaming LTL operations ---
//
// Expected call sequence: SetProperties → StartStream → SendFrame* → EndStream.
// StartStream resets the extraction cache and last-frame tracking.
// SetProperties may be called again after EndStream to install new properties.

// SetProperties installs LTL properties for stream monitoring.
// Automatically derives diagnostic metadata from the formula structure for
// violation enrichment.
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) SetProperties(ctx context.Context, properties []Formula) error {
	props := make([]map[string]any, 0, len(properties))
	for _, f := range properties {
		m, err := serializeFormula(f)
		if err != nil {
			return err
		}
		props = append(props, m)
	}
	cmd, err := serializeCommand("setProperties", map[string]any{
		"properties": props,
	})
	if err != nil {
		return err
	}
	// Hold lock for both the backend call and the diagnostics update
	// to prevent SendFrame from seeing stale diags between the two.
	release, err := c.acquire(ctx, "SetProperties")
	if err != nil {
		return err
	}
	defer release()
	resp, err := c.processLocked(cmd)
	if err != nil {
		return err
	}
	if err := parseSuccessResponse(resp); err != nil {
		return err
	}
	// Build into a temp slice first: buildDiagnostic renders predicate
	// thresholds via the kernel and fails if the GHC runtime is not up (a
	// mock-backend client with no FFIBackend), so a failure must not leave
	// c.diags half-populated.
	diags := make([]PropertyDiagnostic, len(properties))
	for i, f := range properties {
		d, err := buildDiagnostic(f)
		if err != nil {
			return err
		}
		diags[i] = d
	}
	c.diags = diags
	c.cache = newExtractCache()
	if c.logger != nil {
		c.logger.LogAttrs(ctx, slog.LevelInfo, "properties.set",
			slog.Int("count", len(properties)))
	}
	return nil
}

// AddChecks extracts formulas from the given checks, prepends any default checks
// set via WithDefaultChecks, and calls SetProperties.
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) AddChecks(ctx context.Context, checks []CheckResult) error {
	all := make([]Formula, 0, len(c.defaultChecks)+len(checks))
	for _, dc := range c.defaultChecks {
		all = append(all, dc.Formula())
	}
	for _, ch := range checks {
		all = append(all, ch.Formula())
	}
	return c.SetProperties(ctx, all)
}

// StartStream begins a new LTL monitoring stream.
// SetProperties must be called before StartStream.
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) StartStream(ctx context.Context) error {
	// Hold lock for both the backend call and the cache clear
	// to prevent SendFrame from using a stale cache.
	release, err := c.acquire(ctx, "StartStream")
	if err != nil {
		return err
	}
	defer release()
	if c.closed {
		return stateError("client is closed")
	}
	resp, err := c.backend.StartStreamBinary(c.state)
	if err != nil {
		return err
	}
	if err := parseSuccessResponse(resp); err != nil {
		return err
	}
	if c.cache != nil {
		c.cache.clear()
	}
	// Track last frames only when diagnostics are set — lastFrames feeds EOS
	// enrichment, which requires diags. Matches Python's conditional tracking.
	if c.diags != nil {
		c.lastFrames = make(map[uint64]lastFrameData)
	} else {
		c.lastFrames = nil
	}
	if c.logger != nil {
		c.logger.LogAttrs(ctx, slog.LevelInfo, "stream.started")
	}
	return nil
}

// SendFrame sends a CAN frame to the active monitoring stream.
// Returns Ack or Violation depending on whether any property was violated.
// Violations are automatically enriched with signal values and a human-readable
// formula description when diagnostics are available.
// For batch operations, see [Client.SendFrames].
//
// CAN-FD BRS / ESI bits (ISO 11898-1:2015 §10.4.2 / §10.4.3) are
// passed as *bool — pass nil for CAN 2.0B frames where the bits do
// not exist on the wire.  The Aletheia kernel does not consume
// BRS / ESI; they are pass-through metadata for binding consumers
// and the JSON wire shape.
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) SendFrame(
	ctx context.Context, ts Timestamp,
	id CANID, dlc DLC, data FramePayload,
	brs *bool, esi *bool,
) (FrameResponse, error) {
	release, err := c.acquire(ctx, "SendFrame")
	if err != nil {
		return nil, err
	}
	defer release()
	return c.sendFrameLocked(ctx, ts, id, dlc, data, brs, esi)
}

// SendFrames sends multiple CAN frames in a single batch, amortizing lock
// acquisition. The batch is atomic: no other goroutine can interleave frames
// between members. Returns a response for each frame. A [Violation] is a normal
// response and does not stop the batch. Processing stops at the first transport
// or validation error; earlier successful responses are still returned.
//
// Honors ctx cancellation at frame boundaries (commit-prefix-and-report per
// CANCELLATION.md §3.2): if ctx fires mid-batch, the returned slice contains
// the responses for the committed prefix and the wrapped ctx.Err() is the
// returned error. The remaining frames after the cancellation point are NOT
// sent to the FFI; the caller can resume by re-calling SendFrames with the
// uncommitted suffix.
func (c *Client) SendFrames(ctx context.Context, frames []Frame) ([]FrameResponse, error) {
	release, err := c.acquire(ctx, "SendFrames")
	if err != nil {
		return nil, err
	}
	defer release()
	results := make([]FrameResponse, 0, len(frames))
	for i, f := range frames {
		// Per-frame ctx check between FFI calls — the cancellation
		// boundary in batch mode. The most recent FFI call (if one was
		// in flight when ctx fired) ran to completion and was appended.
		if err := ctx.Err(); err != nil {
			return results, fmt.Errorf("SendFrames: %w", err)
		}
		resp, err := c.sendFrameLocked(ctx, f.Timestamp, f.ID, f.DLC, f.Data, f.BRS, f.ESI)
		if err != nil {
			return results, fmt.Errorf("SendFrames frame %d: %w", i, err)
		}
		results = append(results, resp)
	}
	return results, nil
}

// SendFramesSeq sends frames lazily, yielding one (FrameResponse, error) pair
// per frame as the returned [iter.Seq2] is ranged. It is the streaming variant
// of [Client.SendFrames] — the same relationship as strings.SplitSeq to
// strings.Split — and the Go analogue of Python's send_frames_iter.
//
// Use it when the source is a live producer (a channel, a socket, a log
// reader): frames are pulled from the input one at a time and each response is
// yielded immediately, so neither the full input slice nor the full response
// slice is ever materialized. Wrap an existing slice with slices.Values:
//
//	for resp, err := range client.SendFramesSeq(ctx, slices.Values(frames)) {
//		if err != nil { /* handle; iteration has stopped */ break }
//		_ = resp
//	}
//
// Contract (commit-prefix-and-report, per CANCELLATION.md §3.2): each yielded
// (resp, nil) is a frame already committed to the stream state — durable, not
// rolled back. On the first failing frame the sequence yields (nil, err) once
// and then ends; no frame after a failure is sent. Cancellation is the standard
// range protocol: break the loop (or let ctx fire) and the remaining frames are
// never sent, while every pair already yielded stays committed.
//
// The returned sequence is SINGLE-USE: range it exactly once. Unlike
// strings.SplitSeq (pure, so harmless to re-range), this sends to a stateful
// stream — ranging the same returned value twice would re-send the frames and
// corrupt the stream. The peer bindings are single-use by construction (a
// consumed Iterator/Stream/generator); Go's iter.Seq2 is a re-invocable
// closure, so this is a caller obligation rather than a type guarantee.
//
// Locking differs from SendFrames deliberately: SendFrames holds the client
// lock for the whole batch (atomic — no goroutine can interleave). This form
// acquires and releases per frame, never across a yield, because the consumer
// paces the stream and holding the lock across arbitrary consumer code would
// starve Close and any concurrent caller for an unbounded time (matching
// Python's per-frame-locked lazy form). Consequently another goroutine's call
// may interleave between this stream's frames; a single stream is sequential, so
// concurrent streaming on one client is already a misuse.
func (c *Client) SendFramesSeq(ctx context.Context, frames iter.Seq[Frame]) iter.Seq2[FrameResponse, error] {
	return func(yield func(FrameResponse, error) bool) {
		i := 0
		for f := range frames {
			// Per-frame acquire (ctx-aware) + release BEFORE the yield — never
			// hold the lock across consumer code (the 1-deep semaphore would
			// deadlock a re-entrant consumer and starve Close otherwise).
			release, err := c.acquire(ctx, "SendFramesSeq")
			if err != nil {
				yield(nil, err) // acquire already wraps with the method name
				return
			}
			// Release via defer (not an explicit call) so a panic between acquire
			// and the FFI return cannot leak the 1-deep semaphore and deadlock the
			// client forever — matching SendFrames' panic-safety. The closure
			// returns (so release runs) BEFORE the yield, so the lock is never
			// held across consumer code.
			resp, err := func() (FrameResponse, error) {
				defer release()
				return c.sendFrameLocked(ctx, f.Timestamp, f.ID, f.DLC, f.Data, f.BRS, f.ESI)
			}()
			if err != nil {
				yield(nil, fmt.Errorf("SendFramesSeq frame %d: %w", i, err))
				return
			}
			if !yield(resp, nil) {
				return // consumer stopped — commit-prefix; remaining frames unsent
			}
			i++
		}
	}
}

// SendError sends a CAN error event (no ID, no payload). Error frames signal
// a bus error detected by a CAN controller and are acknowledged without LTL
// evaluation — they carry no payload for signal extraction.
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) SendError(ctx context.Context, ts Timestamp) error {
	release, err := c.acquire(ctx, "SendError")
	if err != nil {
		return err
	}
	defer release()
	if c.closed {
		return stateError("client is closed")
	}
	if ts.Microseconds < 0 {
		return validationError("timestamp must be non-negative")
	}
	resp, err := c.backend.SendErrorBinary(c.state, ts)
	if err != nil {
		return err
	}
	if err := parseEventAck(resp); err != nil {
		return err
	}
	if c.logger != nil && c.logger.Enabled(ctx, slog.LevelDebug) {
		c.logger.LogAttrs(ctx, slog.LevelDebug, "error_event.sent",
			slog.Int64("ts", ts.Microseconds), slog.String("response", "ack"))
	}
	return nil
}

// SendRemote sends a CAN remote frame event (ID but no payload). Remote frames
// request transmission of the data frame with a matching ID (CAN 2.0B only;
// deprecated in CAN-FD). Acknowledged without LTL evaluation.
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) SendRemote(ctx context.Context, ts Timestamp, id CANID) error {
	release, err := c.acquire(ctx, "SendRemote")
	if err != nil {
		return err
	}
	defer release()
	if c.closed {
		return stateError("client is closed")
	}
	if ts.Microseconds < 0 {
		return validationError("timestamp must be non-negative")
	}
	resp, err := c.backend.SendRemoteBinary(c.state, ts, id)
	if err != nil {
		return err
	}
	if err := parseEventAck(resp); err != nil {
		return err
	}
	if c.logger != nil && c.logger.Enabled(ctx, slog.LevelDebug) {
		c.logger.LogAttrs(ctx, slog.LevelDebug, "remote_event.sent",
			slog.Int64("ts", ts.Microseconds), slog.Uint64("canId", uint64(id.Value())),
			slog.Bool("extended", id.IsExtended()), slog.String("response", "ack"))
	}
	return nil
}

// sendFrameLocked is the inner implementation of SendFrame. Caller must hold
// the client lock.  ctx is forwarded to slog so request-scoped attrs (trace
// IDs, etc.) propagate into the structured-log records.
func (c *Client) sendFrameLocked(
	ctx context.Context, ts Timestamp,
	id CANID, dlc DLC, data FramePayload,
	brs *bool, esi *bool,
) (FrameResponse, error) {
	if c.closed {
		return nil, stateError("client is closed")
	}
	if ts.Microseconds < 0 {
		return nil, validationError("timestamp must be non-negative")
	}
	if err := validatePayload(dlc, data); err != nil {
		return nil, err
	}
	resp, err := c.backend.SendFrameBinary(c.state, ts, id, dlc, []byte(data), brs, esi)
	if err != nil {
		return nil, err
	}
	fr, err := parseFrameResponse(resp)
	if err != nil {
		return nil, err
	}
	// Track last frame per CAN ID for EOS enrichment.
	// Copy data to prevent caller mutation from corrupting stored frames.
	if c.lastFrames != nil {
		dataCopy := make(FramePayload, len(data))
		copy(dataCopy, data)
		c.lastFrames[canIDKey(id)] = lastFrameData{id: id, dlc: dlc, data: dataCopy}
	}
	// Frame responses are Ack | PropertyBatch.
	// PropertyBatch carries mid-stream Satisfactions (Verdict==Holds)
	// followed by an optional terminal Violation (Verdict==Fails);
	// enrich every fails entry in source-order so the binding's user
	// sees signal diagnostics on each violation in the batch.  Use the
	// per-frame FFI extraction path (with extraction cache) — mirrors
	// the enrichViolation behaviour, NOT enrichEndOfStream
	// (which uses last-known frames and is the EndStream pattern).
	if b, ok := fr.(PropertyBatch); ok && c.diags != nil {
		for i := range b.Results {
			if b.Results[i].Verdict == Fails {
				c.enrichStreamingViolation(ctx, &b.Results[i], id, dlc, data)
			}
		}
		fr = b
	}
	if c.logger != nil && c.logger.Enabled(ctx, slog.LevelDebug) {
		response := "ack"
		if b, ok := fr.(PropertyBatch); ok {
			response = "satisfaction"
			for _, r := range b.Results {
				if r.Verdict == Fails {
					response = "violation"
					break
				}
			}
		}
		c.logger.LogAttrs(ctx, slog.LevelDebug, "frame.processed",
			slog.Int64("ts", ts.Microseconds), slog.Uint64("canId", uint64(id.Value())),
			slog.Bool("extended", id.IsExtended()), slog.String("response", response))
	}
	return fr, nil
}

// EndStream finalizes the monitoring stream and returns verdicts for all properties.
// Failed and Unresolved verdicts are enriched with signal names, formula description,
// and the most recent signal values per CAN ID when available. Earlier frames in the
// stream are not retained.
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) EndStream(ctx context.Context) (*StreamResult, error) {
	release, err := c.acquire(ctx, "EndStream")
	if err != nil {
		return nil, err
	}
	defer release()
	if c.closed {
		return nil, stateError("client is closed")
	}
	resp, err := c.backend.EndStreamBinary(c.state)
	if err != nil {
		return nil, err
	}
	sr, err := parseStreamResponse(resp)
	if err != nil {
		return nil, err
	}
	numFails := 0
	numUnresolved := 0
	for i := range sr.Results {
		switch sr.Results[i].Verdict {
		case Fails:
			numFails++
		case Unresolved:
			numUnresolved++
		}
	}
	c.enrichEndOfStream(ctx, sr.Results)
	c.lastFrames = nil
	if c.logger != nil {
		for _, w := range sr.Warnings {
			if w.Kind == "uncached_atom" {
				c.logger.LogAttrs(ctx, slog.LevelWarn, "endstream.uncached_atom",
					slog.Int("property_index", w.PropertyIndex),
					slog.String("detail", w.Detail))
			}
		}
		c.logger.LogAttrs(ctx, slog.LevelInfo, "stream.ended",
			slog.Int("numResults", len(sr.Results)),
			slog.Int("numFails", numFails),
			slog.Int("numUnresolved", numUnresolved),
			slog.Int("numWarnings", len(sr.Warnings)))
	}
	return sr, nil
}

// enrichStreamingViolation adds a ViolationEnrichment to a streaming
// violation entry (PropertyResult with Verdict == Fails inside a
// PropertyBatch).  Uses the per-frame FFI extraction path via
// extractSignalValues (cached), matching the enrichViolation
// behaviour.  Distinct from enrichEndOfStream, which is the
// EndStream path and uses last-known frames rather than the current
// frame's payload.  Caller must hold the client lock.
func (c *Client) enrichStreamingViolation(ctx context.Context, pr *PropertyResult, id CANID, dlc DLC, data FramePayload) {
	idx := int(pr.PropertyIndex)
	if idx >= len(c.diags) {
		if c.logger != nil {
			c.logger.LogAttrs(ctx, slog.LevelWarn, "enrichment.property_index_oob",
				slog.Int("index", idx), slog.Int("count", len(c.diags)))
		}
		return
	}
	diag := c.diags[idx]
	values := c.extractSignalValues(ctx, diag, id, dlc, data)
	reason := formatEnrichedReason(diag, values, pr.Reason)
	pr.Enrichment = &ViolationEnrichment{
		Signals:        values,
		FormulaDesc:    diag.FormulaDesc,
		EnrichedReason: reason,
		CoreReason:     pr.Reason,
	}
}

// enrichEndOfStream adds a ViolationEnrichment to every Fails/Unresolved
// result, extracting each last-seen frame at most once per EndStream (the
// uniform cross-binding extract-once shape).
//
// Three passes: collect the results to enrich (warning on and excluding any
// out-of-bounds property index); run ONE full-frame extraction per last-seen
// frame, merging every extracted signal first-frame-wins and breaking early
// once every signal wanted by any collected diagnostic has a value; then
// distribute the merged values to each result, filtered to the signals its
// own diagnostic references. A failed frame extraction warns
// enrichment.extraction_failed once per frame per EndStream. When no
// collected diagnostic wants any signal the frame pass is skipped entirely
// (zero FFI calls), but every collected result still gets an enrichment with
// the formula-description fallback reason.
//
// Caller must hold the client lock.  ctx is forwarded to slog so
// request-scoped attrs propagate into structured-log records.
func (c *Client) enrichEndOfStream(ctx context.Context, results []PropertyResult) {
	if len(c.diags) == 0 {
		return
	}
	type pending struct {
		pr   *PropertyResult
		diag PropertyDiagnostic
	}
	var todo []pending
	for i := range results {
		pr := &results[i]
		if pr.Verdict != Fails && pr.Verdict != Unresolved {
			continue
		}
		idx := int(pr.PropertyIndex)
		if idx >= len(c.diags) {
			if c.logger != nil {
				c.logger.LogAttrs(ctx, slog.LevelWarn, "enrichment.property_index_oob",
					slog.Int("index", idx), slog.Int("count", len(c.diags)))
			}
			continue
		}
		todo = append(todo, pending{pr: pr, diag: c.diags[idx]})
	}
	if len(todo) == 0 {
		return
	}
	// Union of signal names wanted by any pending diagnostic; doubles as the
	// remaining-set that drives the early break below.
	remaining := make(map[SignalName]bool)
	for _, p := range todo {
		for _, s := range p.diag.Signals {
			remaining[s] = true
		}
	}
	merged := make(map[SignalName]Rational)
	if len(remaining) > 0 {
		// Sort map keys for deterministic enrichment output in the
		// cross-binding order: ascending CAN ID value, then standard before
		// extended. canIDKey packs the extended flag at bit 32, so a plain
		// uint64 sort would order (extended, value); decode the two halves
		// and compare (value, extended) instead.
		keys := make([]uint64, 0, len(c.lastFrames))
		for k := range c.lastFrames {
			keys = append(keys, k)
		}
		slices.SortFunc(keys, func(a, b uint64) int {
			if r := cmp.Compare(a&0xFFFFFFFF, b&0xFFFFFFFF); r != 0 {
				return r
			}
			return cmp.Compare(a&extendedIDFlag, b&extendedIDFlag)
		})
		for _, k := range keys {
			lf := c.lastFrames[k]
			result := c.extractSignalsLocked(ctx, lf.id, lf.dlc, lf.data)
			if result == nil {
				if c.logger != nil {
					c.logger.LogAttrs(ctx, slog.LevelWarn, "enrichment.extraction_failed",
						slog.Uint64("canId", uint64(lf.id.Value())))
				}
				continue
			}
			for _, sv := range result.Values {
				if _, ok := merged[sv.Name]; !ok {
					merged[sv.Name] = sv.Value
				}
				delete(remaining, sv.Name)
			}
			if len(remaining) == 0 {
				break
			}
		}
	}
	for _, p := range todo {
		var values map[SignalName]Rational
		for _, sig := range p.diag.Signals {
			if val, ok := merged[sig]; ok {
				if values == nil {
					values = make(map[SignalName]Rational)
				}
				values[sig] = val
			}
		}
		p.pr.Enrichment = &ViolationEnrichment{
			Signals:        values,
			FormulaDesc:    p.diag.FormulaDesc,
			EnrichedReason: formatEnrichedReason(p.diag, values, p.pr.Reason),
			CoreReason:     p.pr.Reason,
		}
	}
}

// extractSignalValues extracts signal values for a diagnostic from a frame, using the cache.
// Caller must hold the client lock.  ctx is forwarded to slog so request-scoped
// attrs propagate into structured-log records.
func (c *Client) extractSignalValues(ctx context.Context, diag PropertyDiagnostic, id CANID, dlc DLC, data FramePayload) map[SignalName]Rational {
	if c.cache == nil {
		return nil
	}
	meta := frameMeta{idValue: id.Value(), isExtended: id.IsExtended(), dlc: dlc.Value()}
	result, ok := c.cache.get(meta, data)
	if ok {
		if c.logger != nil && c.logger.Enabled(ctx, slog.LevelDebug) {
			c.logger.LogAttrs(ctx, slog.LevelDebug, "cache.hit",
				slog.Uint64("canId", uint64(id.Value())), slog.Uint64("dlc", uint64(dlc.Value())))
		}
	} else {
		if c.logger != nil && c.logger.Enabled(ctx, slog.LevelDebug) {
			c.logger.LogAttrs(ctx, slog.LevelDebug, "cache.miss",
				slog.Uint64("canId", uint64(id.Value())), slog.Uint64("dlc", uint64(dlc.Value())))
		}
		result = c.extractSignalsLocked(ctx, id, dlc, data)
		if result != nil {
			if !c.cache.put(meta, data, result) && c.logger != nil {
				c.logger.LogAttrs(ctx, slog.LevelWarn, "cache.full",
					slog.Int("size", maxExtractCache))
			}
		}
	}
	if result == nil {
		if c.logger != nil {
			c.logger.LogAttrs(ctx, slog.LevelWarn, "enrichment.extraction_failed",
				slog.Uint64("canId", uint64(id.Value())))
		}
		return nil
	}
	values := make(map[SignalName]Rational)
	for _, sig := range diag.Signals {
		if val, found := result.Get(sig); found {
			values[sig] = val
		}
	}
	if len(values) == 0 {
		return nil
	}
	return values
}

// extractSignalsLocked performs signal extraction via binary FFI. Caller must
// hold the client lock.  ctx is forwarded to slog so request-scoped attrs
// propagate into structured-log records.
//
// Mirrors the ErrBinaryPathUnsupported fallback contract in the public
// [Client.ExtractSignals]: only that sentinel triggers the JSON fallback —
// any other error from ExtractSignalsBin is a real failure (decode / truncation /
// genuine FFI error) and is logged + surfaced as nil. The fall-through is what
// lets a MockBackend-backed Client yield enrichment through the JSON path even
// after a DBC has populated the signal-name cache.
func (c *Client) extractSignalsLocked(ctx context.Context, id CANID, dlc DLC, data FramePayload) *ExtractionResult {
	// Use binary path when signal name cache is populated.
	key := canIDKey(id)
	if names, ok := c.signalNames[key]; ok {
		buf, err := c.backend.ExtractSignalsBin(c.state, id, dlc, []byte(data))
		if err == nil {
			result, perr := parseExtractionBin(buf, names)
			if perr != nil {
				if c.logger != nil {
					c.logger.LogAttrs(ctx, slog.LevelWarn, "extraction.parse_failed",
						slog.Uint64("canId", uint64(id.Value())), slog.String("error", perr.Error()))
				}
				return nil
			}
			return result
		}
		if !errors.Is(err, ErrBinaryPathUnsupported) {
			if c.logger != nil {
				c.logger.LogAttrs(ctx, slog.LevelWarn, "extraction.process_failed",
					slog.Uint64("canId", uint64(id.Value())), slog.String("error", err.Error()))
			}
			return nil
		}
		// ErrBinaryPathUnsupported: fall through to JSON path (e.g. MockBackend).
	}

	// Fallback: JSON path. Reachable either when the signal-name cache is
	// empty, or when the binary path returned ErrBinaryPathUnsupported above.
	resp, err := c.backend.ExtractSignalsBinary(c.state, id, dlc, []byte(data))
	if err != nil {
		if c.logger != nil {
			c.logger.LogAttrs(ctx, slog.LevelWarn, "extraction.process_failed",
				slog.Uint64("canId", uint64(id.Value())), slog.String("error", err.Error()))
		}
		return nil
	}
	result, err := parseExtractionResponse(resp)
	if err != nil {
		if c.logger != nil {
			c.logger.LogAttrs(ctx, slog.LevelWarn, "extraction.parse_failed",
				slog.Uint64("canId", uint64(id.Value())), slog.String("error", err.Error()))
		}
		return nil
	}
	return result
}
