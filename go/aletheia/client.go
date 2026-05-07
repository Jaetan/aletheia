package aletheia

import (
	"context"
	"errors"
	"fmt"
	"io"
	"log/slog"
	"math"
	"slices"
	"sync"
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
func (c *Client) lock(ctx context.Context) error {
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

// processLocked sends input to the backend. Caller must hold the client lock.
func (c *Client) processLocked(input string) (string, error) {
	if c.closed {
		return "", stateError("client is closed")
	}
	return c.backend.Process(c.state, input)
}

// lastFrameData stores the last frame seen for a CAN ID, for EOS enrichment.
type lastFrameData struct {
	id   CanID
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

const rationalDenominator int64 = 1_000_000_000

// floatToRational converts a float64 to (numerator, denominator) using 10^9 scaling.
// Precision: 9 decimal digits (~1 ppb). The Haskell side normalizes to coprime form via GCD.
// Returns an error for Inf, NaN, or values that overflow int64 when scaled.
func floatToRational(value float64) (int64, int64, error) {
	if math.IsInf(value, 0) || math.IsNaN(value) {
		return 0, 0, validationError(fmt.Sprintf("cannot convert %v to rational", value))
	}
	const limit = math.MaxInt64/rationalDenominator - 1
	if value > float64(limit) || value < -float64(limit) {
		return 0, 0, validationError(fmt.Sprintf("value %g overflows int64 when scaled to rational", value))
	}
	return int64(math.Round(value * float64(rationalDenominator))), rationalDenominator, nil
}

// resolveSignalIndices looks up signal names in the cached index and converts values to rationals.
// Returns parallel arrays of (indices, numerators, denominators).
func (c *Client) resolveSignalIndices(signals []SignalValue, id CanID, cmdName string) ([]uint32, []int64, []int64, error) {
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
		n, d, err := floatToRational(float64(sv.Value))
		if err != nil {
			return nil, nil, nil, fmt.Errorf("%s: signal %q: %w", cmdName, sv.Name, err)
		}
		indices = append(indices, uint32(idx))
		nums = append(nums, n)
		dens = append(dens, d)
	}
	return indices, nums, dens, nil
}

// --- DBC operations ---

// populateSignalLookup rebuilds the name-to-index lookup from a parsed DBC.
// Both ParseDBC and ParseDBCText call this after the Agda core returns
// a validated body so subsequent BuildFrame/UpdateFrame calls can resolve
// signal names against the canonical (post-validation) DBC.
func (c *Client) populateSignalLookup(dbc DbcDefinition) {
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
func (c *Client) ParseDBC(ctx context.Context, dbc DbcDefinition) (*ParsedDBC, error) {
	dbcMap, err := serializeDBC(dbc)
	if err != nil {
		return nil, err
	}
	cmd, err := serializeCommand("parseDBC", map[string]any{
		"dbc": dbcMap,
	})
	if err != nil {
		return nil, err
	}
	if err := c.lock(ctx); err != nil {
		return nil, fmt.Errorf("ParseDBC: %w", err)
	}
	defer c.unlock()
	if err := ctx.Err(); err != nil {
		return nil, fmt.Errorf("ParseDBC: %w", err)
	}
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
		c.logger.Info("dbc.parsed", "messages", len(parsed.DBC.Messages), "warnings", len(parsed.Warnings))
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
	cmd, err := serializeCommand("parseDBCText", map[string]any{
		"text": text,
	})
	if err != nil {
		return nil, err
	}
	if err := c.lock(ctx); err != nil {
		return nil, fmt.Errorf("ParseDBCText: %w", err)
	}
	defer c.unlock()
	if err := ctx.Err(); err != nil {
		return nil, fmt.Errorf("ParseDBCText: %w", err)
	}
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
		c.logger.Info("dbc.text_parsed", "messages", len(parsed.DBC.Messages), "warnings", len(parsed.Warnings))
	}
	return parsed, nil
}

// ValidateDBC checks a DBC definition for structural issues (overlapping signals,
// factor-zero, DLC violations, etc.) and returns all found issues.
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) ValidateDBC(ctx context.Context, dbc DbcDefinition) (*ValidationResult, error) {
	dbcMap, err := serializeDBC(dbc)
	if err != nil {
		return nil, err
	}
	cmd, err := serializeCommand("validateDBC", map[string]any{
		"dbc": dbcMap,
	})
	if err != nil {
		return nil, err
	}
	if err := c.lock(ctx); err != nil {
		return nil, fmt.Errorf("ValidateDBC: %w", err)
	}
	defer c.unlock()
	if err := ctx.Err(); err != nil {
		return nil, fmt.Errorf("ValidateDBC: %w", err)
	}
	resp, err := c.processLocked(cmd)
	if err != nil {
		return nil, err
	}
	return parseValidationResponse(resp)
}

// FormatDBC returns the currently loaded DBC definition as parsed by the Agda core.
// Call ParseDBC first.
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) FormatDBC(ctx context.Context) (*DbcDefinition, error) {
	if err := c.lock(ctx); err != nil {
		return nil, fmt.Errorf("FormatDBC: %w", err)
	}
	defer c.unlock()
	if err := ctx.Err(); err != nil {
		return nil, fmt.Errorf("FormatDBC: %w", err)
	}
	if c.closed {
		return nil, stateError("client is closed")
	}
	resp, err := c.backend.FormatDbcBinary(c.state)
	if err != nil {
		return nil, err
	}
	return parseDbcResponse(resp)
}

// FormatDBCText renders a DbcDefinition as .dbc file text via the verified
// Agda formatter.  Inverse of [Client.ParseDBCText] at the wire level:
// ParseDBCText(FormatDBCText(d)) returns d byte-identical for any well-formed
// DBC (Phase E.9a coverage).  Does not modify client state — pass any
// DbcDefinition value (typically from ParseDBCText, FormatDBC, or a JSON load).
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) FormatDBCText(ctx context.Context, dbc DbcDefinition) (string, error) {
	dbcMap, err := serializeDBC(dbc)
	if err != nil {
		return "", err
	}
	cmd, err := serializeCommand("formatDBCText", map[string]any{
		"dbc": dbcMap,
	})
	if err != nil {
		return "", err
	}
	if err := c.lock(ctx); err != nil {
		return "", fmt.Errorf("FormatDBCText: %w", err)
	}
	defer c.unlock()
	if err := ctx.Err(); err != nil {
		return "", fmt.Errorf("FormatDBCText: %w", err)
	}
	resp, err := c.processLocked(cmd)
	if err != nil {
		return "", err
	}
	return parseDbcTextResponse(resp)
}

// --- Signal operations ---

// ExtractSignals decodes all signals from a CAN frame using the loaded DBC.
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) ExtractSignals(ctx context.Context, id CanID, dlc DLC, data FramePayload) (*ExtractionResult, error) {
	if err := validatePayload(dlc, data); err != nil {
		return nil, err
	}
	if err := c.lock(ctx); err != nil {
		return nil, fmt.Errorf("ExtractSignals: %w", err)
	}
	defer c.unlock()
	if err := ctx.Err(); err != nil {
		return nil, fmt.Errorf("ExtractSignals: %w", err)
	}
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
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) BuildFrame(ctx context.Context, id CanID, signals []SignalValue, dlc DLC) (FramePayload, error) {
	if err := c.lock(ctx); err != nil {
		return nil, fmt.Errorf("BuildFrame: %w", err)
	}
	defer c.unlock()
	if err := ctx.Err(); err != nil {
		return nil, fmt.Errorf("BuildFrame: %w", err)
	}
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
func (c *Client) UpdateFrame(ctx context.Context, id CanID, dlc DLC, data FramePayload, signals []SignalValue) (FramePayload, error) {
	if err := validatePayload(dlc, data); err != nil {
		return nil, err
	}
	if err := c.lock(ctx); err != nil {
		return nil, fmt.Errorf("UpdateFrame: %w", err)
	}
	defer c.unlock()
	if err := ctx.Err(); err != nil {
		return nil, fmt.Errorf("UpdateFrame: %w", err)
	}
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
	if err := c.lock(ctx); err != nil {
		return fmt.Errorf("SetProperties: %w", err)
	}
	defer c.unlock()
	if err := ctx.Err(); err != nil {
		return fmt.Errorf("SetProperties: %w", err)
	}
	resp, err := c.processLocked(cmd)
	if err != nil {
		return err
	}
	if err := parseSuccessResponse(resp); err != nil {
		return err
	}
	c.diags = make([]PropertyDiagnostic, len(properties))
	for i, f := range properties {
		c.diags[i] = BuildDiagnostic(f)
	}
	c.cache = newExtractCache()
	if c.logger != nil {
		c.logger.Info("properties.set", "count", len(properties))
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
	if err := c.lock(ctx); err != nil {
		return fmt.Errorf("StartStream: %w", err)
	}
	defer c.unlock()
	if err := ctx.Err(); err != nil {
		return fmt.Errorf("StartStream: %w", err)
	}
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
		c.logger.Info("stream.started")
	}
	return nil
}

// SendFrame sends a CAN frame to the active monitoring stream.
// Returns Ack or Violation depending on whether any property was violated.
// Violations are automatically enriched with signal values and a human-readable
// formula description when diagnostics are available.
// For batch operations, see [Client.SendFrames].
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) SendFrame(ctx context.Context, ts Timestamp, id CanID, dlc DLC, data FramePayload) (FrameResponse, error) {
	if err := c.lock(ctx); err != nil {
		return nil, fmt.Errorf("SendFrame: %w", err)
	}
	defer c.unlock()
	if err := ctx.Err(); err != nil {
		return nil, fmt.Errorf("SendFrame: %w", err)
	}
	return c.sendFrameLocked(ts, id, dlc, data)
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
	if err := c.lock(ctx); err != nil {
		return nil, fmt.Errorf("SendFrames: %w", err)
	}
	defer c.unlock()
	if err := ctx.Err(); err != nil {
		return nil, fmt.Errorf("SendFrames: %w", err)
	}
	results := make([]FrameResponse, 0, len(frames))
	for i, f := range frames {
		// Per-frame ctx check between FFI calls — the cancellation
		// boundary in batch mode. The most recent FFI call (if one was
		// in flight when ctx fired) ran to completion and was appended.
		if err := ctx.Err(); err != nil {
			return results, fmt.Errorf("SendFrames: %w", err)
		}
		resp, err := c.sendFrameLocked(f.Timestamp, f.ID, f.DLC, f.Data)
		if err != nil {
			return results, fmt.Errorf("frame %d: %w", i, err)
		}
		results = append(results, resp)
	}
	return results, nil
}

// SendError sends a CAN error event (no ID, no payload). Error frames signal
// a bus error detected by a CAN controller and are acknowledged without LTL
// evaluation — they carry no payload for signal extraction.
//
// Honors ctx cancellation per the contract on [Client.ParseDBC].
func (c *Client) SendError(ctx context.Context, ts Timestamp) error {
	if err := c.lock(ctx); err != nil {
		return fmt.Errorf("SendError: %w", err)
	}
	defer c.unlock()
	if err := ctx.Err(); err != nil {
		return fmt.Errorf("SendError: %w", err)
	}
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
	if c.logger != nil {
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
func (c *Client) SendRemote(ctx context.Context, ts Timestamp, id CanID) error {
	if err := c.lock(ctx); err != nil {
		return fmt.Errorf("SendRemote: %w", err)
	}
	defer c.unlock()
	if err := ctx.Err(); err != nil {
		return fmt.Errorf("SendRemote: %w", err)
	}
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
	if c.logger != nil {
		c.logger.LogAttrs(ctx, slog.LevelDebug, "remote_event.sent",
			slog.Int64("ts", ts.Microseconds), slog.Uint64("canId", uint64(id.Value())),
			slog.Bool("extended", id.IsExtended()), slog.String("response", "ack"))
	}
	return nil
}

// sendFrameLocked is the inner implementation of SendFrame. Caller must hold
// the client lock.
func (c *Client) sendFrameLocked(ts Timestamp, id CanID, dlc DLC, data FramePayload) (FrameResponse, error) {
	if c.closed {
		return nil, stateError("client is closed")
	}
	if ts.Microseconds < 0 {
		return nil, validationError("timestamp must be non-negative")
	}
	if err := validatePayload(dlc, data); err != nil {
		return nil, err
	}
	resp, err := c.backend.SendFrameBinary(c.state, ts, id, dlc, []byte(data))
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
	if v, ok := fr.(Violation); ok && c.diags != nil {
		c.enrichViolation(&v, id, dlc, data)
		if c.logger != nil {
			c.logger.LogAttrs(context.Background(), slog.LevelDebug, "frame.processed",
				slog.Int64("ts", ts.Microseconds), slog.Uint64("canId", uint64(id.Value())),
				slog.Bool("extended", id.IsExtended()), slog.String("response", "violation"))
		}
		return v, nil
	}
	if c.logger != nil {
		c.logger.LogAttrs(context.Background(), slog.LevelDebug, "frame.processed",
			slog.Int64("ts", ts.Microseconds), slog.Uint64("canId", uint64(id.Value())),
			slog.Bool("extended", id.IsExtended()), slog.String("response", "ack"))
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
	if err := c.lock(ctx); err != nil {
		return nil, fmt.Errorf("EndStream: %w", err)
	}
	defer c.unlock()
	if err := ctx.Err(); err != nil {
		return nil, fmt.Errorf("EndStream: %w", err)
	}
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
			if c.diags != nil {
				c.enrichPropertyResult(&sr.Results[i])
			}
		case Unresolved:
			numUnresolved++
			if c.diags != nil {
				c.enrichPropertyResult(&sr.Results[i])
			}
		}
	}
	c.lastFrames = nil
	if c.logger != nil {
		c.logger.Info("stream.ended", "numResults", len(sr.Results),
			"numFails", numFails, "numUnresolved", numUnresolved)
	}
	return sr, nil
}

// enrichViolation adds a ViolationEnrichment to a Violation. Caller must hold
// the client lock.
func (c *Client) enrichViolation(v *Violation, id CanID, dlc DLC, data FramePayload) {
	idx := int(v.PropertyIndex)
	if idx >= len(c.diags) {
		if c.logger != nil {
			c.logger.LogAttrs(context.Background(), slog.LevelWarn, "enrichment.property_index_oob",
				slog.Int("index", idx), slog.Int("count", len(c.diags)))
		}
		return
	}
	diag := c.diags[idx]
	values := c.extractSignalValues(diag, id, dlc, data)
	reason := formatEnrichedReason(diag, values, v.Reason)
	v.Enrichment = &ViolationEnrichment{
		Signals:        values,
		FormulaDesc:    diag.FormulaDesc,
		EnrichedReason: reason,
		CoreReason:     v.Reason,
	}
}

// enrichPropertyResult adds a ViolationEnrichment to a failed PropertyResult,
// including last-known signal values from tracked frames. Caller must hold
// the client lock.
func (c *Client) enrichPropertyResult(pr *PropertyResult) {
	idx := int(pr.PropertyIndex)
	if idx >= len(c.diags) {
		if c.logger != nil {
			c.logger.LogAttrs(context.Background(), slog.LevelWarn, "enrichment.property_index_oob",
				slog.Int("index", idx), slog.Int("count", len(c.diags)))
		}
		return
	}
	diag := c.diags[idx]
	values := c.extractLastKnownValues(diag)
	reason := formatEnrichedReason(diag, values, pr.Reason)
	pr.Enrichment = &ViolationEnrichment{
		Signals:        values,
		FormulaDesc:    diag.FormulaDesc,
		EnrichedReason: reason,
		CoreReason:     pr.Reason,
	}
}

// extractLastKnownValues extracts signal values from the last-seen frames for
// all signals referenced in a diagnostic. Caller must hold the client lock.
func (c *Client) extractLastKnownValues(diag PropertyDiagnostic) map[SignalName]PhysicalValue {
	if len(c.lastFrames) == 0 || len(diag.Signals) == 0 {
		return nil
	}
	wanted := make(map[SignalName]bool, len(diag.Signals))
	for _, s := range diag.Signals {
		wanted[s] = true
	}
	values := make(map[SignalName]PhysicalValue)
	// Sort map keys for deterministic enrichment output. The uint64 key encodes
	// (CAN ID value, extended flag) via canIDKey, so the natural ordering sorts
	// by value then by extended-flag.
	keys := make([]uint64, 0, len(c.lastFrames))
	for k := range c.lastFrames {
		keys = append(keys, k)
	}
	slices.Sort(keys)
	// Try extraction against all last-seen frames to find matching signals.
	for _, k := range keys {
		lf := c.lastFrames[k]
		result := c.extractSignalsLocked(lf.id, lf.dlc, lf.data)
		if result == nil {
			if c.logger != nil {
				c.logger.LogAttrs(context.Background(), slog.LevelWarn, "enrichment.extraction_failed",
					slog.Uint64("canId", uint64(lf.id.Value())))
			}
			continue
		}
		for _, sv := range result.Values {
			if wanted[sv.Name] {
				values[sv.Name] = sv.Value
				delete(wanted, sv.Name)
			}
		}
		if len(wanted) == 0 {
			break
		}
	}
	if len(values) == 0 {
		return nil
	}
	return values
}

// extractSignalValues extracts signal values for a diagnostic from a frame, using the cache.
// Caller must hold the client lock.
func (c *Client) extractSignalValues(diag PropertyDiagnostic, id CanID, dlc DLC, data FramePayload) map[SignalName]PhysicalValue {
	if c.cache == nil {
		return nil
	}
	key := frameKey{idValue: id.Value(), isExtended: id.IsExtended(), dlc: dlc.Value(), data: string(data)}
	result, ok := c.cache.get(key)
	if ok {
		if c.logger != nil {
			c.logger.LogAttrs(context.Background(), slog.LevelDebug, "cache.hit",
				slog.Uint64("canId", uint64(id.Value())), slog.Uint64("dlc", uint64(dlc.Value())))
		}
	} else {
		if c.logger != nil {
			c.logger.LogAttrs(context.Background(), slog.LevelDebug, "cache.miss",
				slog.Uint64("canId", uint64(id.Value())), slog.Uint64("dlc", uint64(dlc.Value())))
		}
		result = c.extractSignalsLocked(id, dlc, data)
		if result != nil {
			if !c.cache.put(key, result) && c.logger != nil {
				c.logger.LogAttrs(context.Background(), slog.LevelWarn, "cache.full",
					slog.Int("size", maxExtractCache))
			}
		}
	}
	if result == nil {
		if c.logger != nil {
			c.logger.LogAttrs(context.Background(), slog.LevelWarn, "enrichment.extraction_failed",
				slog.Uint64("canId", uint64(id.Value())))
		}
		return nil
	}
	values := make(map[SignalName]PhysicalValue)
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
// hold the client lock.
//
// Mirrors the ErrBinaryPathUnsupported fallback contract in the public
// [Client.ExtractSignals]: only that sentinel triggers the JSON fallback —
// any other error from ExtractSignalsBin is a real failure (decode / truncation /
// genuine FFI error) and is logged + surfaced as nil. The fall-through is what
// lets a MockBackend-backed Client yield enrichment through the JSON path even
// after a DBC has populated the signal-name cache.
func (c *Client) extractSignalsLocked(id CanID, dlc DLC, data FramePayload) *ExtractionResult {
	// Use binary path when signal name cache is populated.
	key := canIDKey(id)
	if names, ok := c.signalNames[key]; ok {
		buf, err := c.backend.ExtractSignalsBin(c.state, id, dlc, []byte(data))
		if err == nil {
			result, perr := parseExtractionBin(buf, names)
			if perr != nil {
				if c.logger != nil {
					c.logger.LogAttrs(context.Background(), slog.LevelWarn, "extraction.parse_failed",
						slog.Uint64("canId", uint64(id.Value())), slog.String("error", perr.Error()))
				}
				return nil
			}
			return result
		}
		if !errors.Is(err, ErrBinaryPathUnsupported) {
			if c.logger != nil {
				c.logger.LogAttrs(context.Background(), slog.LevelWarn, "extraction.process_failed",
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
			c.logger.LogAttrs(context.Background(), slog.LevelWarn, "extraction.process_failed",
				slog.Uint64("canId", uint64(id.Value())), slog.String("error", err.Error()))
		}
		return nil
	}
	result, err := parseExtractionResponse(resp)
	if err != nil {
		if c.logger != nil {
			c.logger.LogAttrs(context.Background(), slog.LevelWarn, "extraction.parse_failed",
				slog.Uint64("canId", uint64(id.Value())), slog.String("error", err.Error()))
		}
		return nil
	}
	return result
}
