// SPDX-FileCopyrightText: 2025 Nicolas Pelletier
// SPDX-License-Identifier: BSD-2-Clause

package aletheia

import (
	"context"
	"fmt"
	"io"
	"log/slog"
	"sync"
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
// A Client is safe for concurrent use from multiple goroutines: calls are
// serialised, because the LTL automaton is sequential, through a 1-deep
// channel semaphore rather than a sync.Mutex, so a goroutine waiting for
// the lock is cancelled by its [context.Context] without ever acquiring
// it, which neither Lock nor TryLock can express. Every operation method
// takes a [context.Context] first; docs/architecture/CANCELLATION.md is the
// contract. Close is one-shot through a sync.Once, so a double close is
// safe. Create with [NewClient]; [Client.Close] implements [io.Closer].
type Client struct {
	backend       Backend
	state         State
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
		// Takes the lock without a context: an in-flight FFI call finishes
		// first, since nothing can preempt the GHC runtime.
		c.lockCh <- struct{}{}
		defer c.unlock()
		if c.state != 0 {
			c.backend.Close(c.state)
			c.state = 0
			c.closed = true
		}
	})
	return nil
}

// lock takes the client lock and returns its release, or returns ctx.Err()
// when ctx is already cancelled or fires while waiting, with a release that
// does nothing, since then no lock is held.
func (c *Client) lock(ctx context.Context) (release func(), err error) {
	select {
	case <-ctx.Done():
		return releaseNothing, ctx.Err()
	case c.lockCh <- struct{}{}:
		return c.unlock, nil
	}
}

// unlock releases the client lock; the caller holds it, and a caller that
// does not is a defect that fails here rather than blocking forever.
func (c *Client) unlock() {
	select {
	case <-c.lockCh:
	default:
		panic("aletheia: unlock of a lock that is not held")
	}
}

// acquire takes the lock for the operation called name, rechecks the
// context once the lock is held (a cancellation between the two would
// otherwise reach the FFI), and refuses a closed client. Every error carries
// the operation name. Every return hands back the release that lock
// returned, which frees the lock exactly when it was taken, and the caller
// defers it before it checks the error, so no branch taken or skipped can
// leave the lock held.
func (c *Client) acquire(ctx context.Context, name string) (release func(), err error) {
	release, err = c.lock(ctx)
	if err != nil {
		return release, fmt.Errorf("%s: %w", name, err)
	}
	if err = ctx.Err(); err != nil {
		return release, fmt.Errorf("%s: %w", name, err)
	}
	if c.closed {
		return release, stateError(name + ": client is closed")
	}
	return release, nil
}

// releaseNothing is the release of an acquire that took no lock.
func releaseNothing() {}

// IsClosed reports whether [Client.Close] has been called.  Acquires
// the same internal lock as the data-path operations so the answer
// reflects committed state (no torn reads).  Cross-binding parity
// with Python's “AletheiaClient.is_closed“ property.
func (c *Client) IsClosed() bool {
	c.lockCh <- struct{}{}
	defer c.unlock()
	return c.closed
}

// processLocked sends input to the backend. Caller must hold the client lock.
func (c *Client) processLocked(input string) (string, error) {
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

// resolveInjections looks up each signal's position in the cached index and pairs it with the exact value to place there.
// Returns parallel arrays of (indices, numerators, denominators).
func (c *Client) resolveInjections(signals []SignalValue, id CANID, cmdName string) ([]SignalInjection, error) {
	if c.signalIndex == nil {
		return nil, stateError(cmdName + ": no DBC loaded (call ParseDBC first)")
	}
	key := canIDKey(id)
	indexMap, ok := c.signalIndex[key]
	if !ok {
		return nil, validationError(fmt.Sprintf("%s: no DBC message for CAN ID %d (extended=%v)", cmdName, id.Value(), id.IsExtended()))
	}
	injections := make([]SignalInjection, 0, len(signals))
	for _, sv := range signals {
		idx, found := indexMap[string(sv.Name)]
		if !found {
			return nil, validationError(fmt.Sprintf("%s: unknown signal %q for CAN ID %d", cmdName, sv.Name, id.Value()))
		}
		// SignalValue.Value is an exact Rational (build via IntRational or the
		// kernel FromDecimal). Validate the denominator the wire requires; a
		// Rational has no NaN/Inf, so only the denominator needs checking.
		if err := validateRational(fmt.Sprintf("%s: signal %q", cmdName, sv.Name), sv.Value); err != nil {
			return nil, err
		}
		injections = append(injections, SignalInjection{
			Index:       uint32(idx),
			Numerator:   sv.Value.Numerator,
			Denominator: sv.Value.Denominator,
		})
	}
	return injections, nil
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
	defer release()
	if err != nil {
		return nil, err
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
	// The kernel bounds the text at MaxDBCTextBytes inside the command, and
	// FFIBackend.Process bounds the whole command at MaxJSONBytes; the text
	// is refused here before a command is built around it.
	if err := refuseOversize(uint64(len(text)), MaxDBCTextBytes); err != nil {
		return nil, err
	}
	cmd, err := serializeCommand("parseDBCText", map[string]any{
		"text": text,
	})
	if err != nil {
		return nil, err
	}
	release, err := c.acquire(ctx, "ParseDBCText")
	defer release()
	if err != nil {
		return nil, err
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
	defer release()
	if err != nil {
		return nil, err
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
func (c *Client) FormatDBC(ctx context.Context) (*DBCDefinition, error) {
	release, err := c.acquire(ctx, "FormatDBC")
	defer release()
	if err != nil {
		return nil, err
	}
	resp, err := c.backend.FormatDBCBinary(c.state)
	if err != nil {
		return nil, err
	}
	return parseDBCResponse(resp)
}

// FormatDBCText renders a DBCDefinition as .dbc text through the verified
// formatter and returns the text with its advisory (warning-severity)
// issues. It is strict: the text comes back only when it provably
// re-parses to the input, a stricter class than validating clean (the
// well-formed DBC entry in docs/GLOSSARY.md); otherwise the call fails
// with a [TextRoundTripFailedError] rather than emitting lossy text. The
// round trip holds at the text-parser level: a DBC with duplicate message
// ids or signal names is emitted with warnings and refused by the
// validating load of ParseDBCText. A definition past a size bound is
// refused before it is formatted, with the [InputBoundExceededError] that
// ParseDBC and ValidateDBC answer for it. Client state is untouched; any
// DBCDefinition value may be passed.
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
	defer release()
	if err != nil {
		return nil, err
	}
	resp, err := c.processLocked(cmd)
	if err != nil {
		return nil, err
	}
	return parseDBCTextResponse(resp)
}
