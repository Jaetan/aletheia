# Aletheia Streaming Protocol

**Purpose**: Complete specification of the FFI protocol for CAN frame analysis with LTL checking. Version and release metadata live in [DISTRIBUTION.md](../development/DISTRIBUTION.md).

---

## Contents

- [Audience](#audience)
- [Overview](#overview)
- [Message Types](#message-types)
- [Commands](#commands)
- [Binary Entry Points](#binary-entry-points)
- [Response Types](#response-types)
- [LTL Property Format](#ltl-property-format)
- [Rational Number Encoding](#rational-number-encoding)
- [Example Session](#example-session)
- [Limits](#limits)
- [Error Handling](#error-handling)
- [Implementation Notes](#implementation-notes)
- [Structured Logging](#structured-logging)
- [See Also](#see-also)

---

## Audience

This document is for:
- Python, C++, Go, and Rust developers integrating the Aletheia client with custom tooling
- Maintainers modifying the JSON protocol or FFI boundary
- System architects understanding the communication layer

**Prerequisites**: Familiarity with JSON and CAN bus basics. No Agda or Haskell knowledge needed.

> Most users don't need this document. See the [Interface Guide](../reference/INTERFACES.md) for Check API, YAML, and Excel workflows, or the [Python API Guide](../reference/PYTHON_API.md) for the `AletheiaClient` reference.

---

## Overview

Aletheia uses a JSON protocol for communication between language bindings (Python, C++, Go, Rust) and the Agda/Haskell core. Each message is a single JSON object passed as a string via FFI (Foreign Function Interface) function calls.

**Communication Model**:
- `aletheia_process()` takes a JSON string: the DBC and property commands (parseDBC, setProperties, validateDBC, parseDBCText, formatDBCText).
- The [binary entry points](#binary-entry-points) take C values: the stream's lifecycle (`aletheia_start_stream()`, `aletheia_end_stream()`), its events (`aletheia_send_frame()`, `aletheia_send_error()`, `aletheia_send_remote()`), extraction (`aletheia_extract_signals()`), the DBC's export (`aletheia_format_dbc()`), and the binary-output build, update and extraction.
- One call per response (request-response)
- Sequential processing (no threading or queuing)
- No subprocess or IPC — everything runs in-process via `libaletheia-ffi.so`

**State Machine**:
~~~
WaitingForDBC → ParseDBC → ReadyToStream → SetProperties → ReadyToStream
                                          → StartStream → Streaming → SendFrame* → Streaming
                                                                     → EndStream → ReadyToStream
~~~

---

## Message Types

All messages have a `"type"` field that determines how they are processed.

### Type Tags
- `"command"`: DBC / property JSON commands — `parseDBC`, `setProperties`, `validateDBC`, `parseDBCText`, `formatDBCText`. The streaming and frame operations have **no JSON command form**; they are the binary entry points: start-stream (`aletheia_start_stream`), send-frame (`aletheia_send_frame`), extract-signals (`aletheia_extract_signals`), format-DBC (`aletheia_format_dbc`), end-stream (`aletheia_end_stream`), and frame build/update (`aletheia_build_frame_bin` / `aletheia_update_frame_bin`).

> **Note**: Data frames are sent via the binary `aletheia_send_frame()` entry point, not as JSON. See [Binary Entry Points](#binary-entry-points) below.

---

## Commands

### ParseDBC

Load a DBC (Database CAN) structure from JSON format.

**Request**:
~~~json
{
  "type": "command",
  "command": "parseDBC",
  "dbc": {
    "version": "1.0",
    "messages": [
      {
        "id": 256,
        "name": "SpeedMessage",
        "dlc": 8,
        "extended": false,
        "sender": "ECU",
        "signals": [
          {
            "name": "Speed",
            "startBit": 0,
            "length": 16,
            "byteOrder": "little_endian",
            "signed": false,
            "factor": 0.1,
            "offset": 0.0,
            "minimum": 0.0,
            "maximum": 300.0,
            "unit": "km/h",
            "presence": "always"
          }
        ]
      }
    ]
  }
}
~~~

**Response** (Success):
~~~json
{
  "status": "success",
  "dbc": { ... },
  "warnings": []
}
~~~

The success response echoes the canonical parsed body (`dbc`) plus `warnings` — the warning-severity validation issues, in the same `{severity, code, detail}` element shape as [ValidateDBC](#validatedbc)'s `issues`. Warnings never block a load; error-severity issues instead refuse it with `handler_validation_failed` (see [§ Wire shape](#wire-shape)).

**Response** (Error):
~~~json
{
  "status": "error",
  "message": "Missing required field: messages"
}
~~~

**Fields**:
- `dbc.version`: DBC format version (currently "1.0")
- `dbc.messages`: Array of CAN message definitions
  - `id`: CAN message ID (0-2047 for standard, 0-536870911 for extended)
  - `name`: Message name (string)
  - `dlc`: Data Length Code (0-15; DLC 0-8 map directly to byte counts, 9→12, 10→16, 11→20, 12→24, 13→32, 14→48, 15→64 bytes for CAN-FD)
  - `extended`: Boolean, true for 29-bit IDs
  - `sender`: Node that sends this message
  - `signals`: Array of signal definitions
    - `name`: Signal name (must be unique within message)
    - `startBit`: Bit position in frame (below the message's frame capacity `dlcToBytes(dlc) * 8`)
    - `length`: Signal length in bits (at least 1, at most the message's frame capacity `dlcToBytes(dlc) * 8`)
    - `byteOrder`: "little_endian" or "big_endian"
    - `signed`: Boolean, true for signed integers
    - `factor`: Scaling factor (rational as decimal)
    - `offset`: Offset applied after scaling
    - `minimum`: Minimum physical value
    - `maximum`: Maximum physical value
    - `presence`: "always" for always-present signals (default if omitted); multiplexed signals use `multiplexor` and `multiplex_values` fields instead (see Multiplexing Support below)

**Signal geometry — frame-capacity bound, refuse posture**. A signal's bit
geometry is bounded by its containing message's frame capacity,
`dlcToBytes(dlc) * 8` bits — the DLC already encodes classic CAN vs CAN-FD, so
there is no separate per-protocol bound. The kernel checks the SUBMITTED
values at entry and refuses out-of-capacity geometry with a typed error naming
them (`parse_signal_start_bit_exceeds_frame`,
`parse_signal_bit_length_exceeds_frame`, `parse_signal_bit_length_zero`;
values are never normalized or clamped into range). For big-endian (Motorola)
signals, `startBit` names the physical MSB and the descending run of `length`
bits must stay inside the frame (`parse_signal_big_endian_overflow`
otherwise); the textbook full-frame layout — MSB at bit 7 descending through
the whole frame — is accepted. Both DBC entry routes (this command and
[ParseDBCText](#dbc-text-parse-errors--parsedbctext--formatdbctext)) run the
same gate and emit the same codes; text-route refusals are anchored by the
signal's name (`signal 'NAME': ...`) rather than a byte position, because the
gate runs after the `SG_` line parses.

**State Transition**: `WaitingForDBC` → `ReadyToStream`

---

### Multiplexing Support

Aletheia supports multiplexed signals (signals that are conditionally present based on a multiplexor signal's value).

**Signal Presence Formats**:

#### Always Present
~~~json
{"presence": "always"}
~~~
Signal is always present in the frame.

#### Conditional Presence (Multiplexed)

Multiplexed signals use flat `multiplexor` and `multiplex_values` fields instead of `presence`:

~~~json
{
  "multiplexor": "MuxSignal",
  "multiplex_values": [1]
}
~~~

Signal is only present when the multiplexor signal's value is in the `multiplex_values` array. Single-value mux uses a one-element array (e.g., `[1]`); extended mux (SG_MUL_VAL_) uses multiple values (e.g., `[0, 1, 3]`). The `presence` field is omitted for multiplexed signals.

**Example** (Multiplexed Message):
~~~json
{
  "id": 512,
  "name": "MultiplexedMessage",
  "dlc": 8,
  "extended": false,
  "sender": "ECU",
  "signals": [
    {
      "name": "MuxSignal",
      "startBit": 0,
      "length": 8,
      "byteOrder": "little_endian",
      "signed": false,
      "factor": 1.0,
      "offset": 0.0,
      "minimum": 0.0,
      "maximum": 3.0,
      "unit": "",
      "presence": "always"
    },
    {
      "name": "Signal_Mux0",
      "startBit": 8,
      "length": 16,
      "byteOrder": "little_endian",
      "signed": false,
      "factor": 1.0,
      "offset": 0.0,
      "minimum": 0.0,
      "maximum": 1000.0,
      "unit": "rpm",
      "multiplexor": "MuxSignal",
      "multiplex_values": [0]
    },
    {
      "name": "Signal_Mux1",
      "startBit": 8,
      "length": 16,
      "byteOrder": "little_endian",
      "signed": true,
      "factor": 0.1,
      "offset": 0.0,
      "minimum": -50.0,
      "maximum": 150.0,
      "unit": "°C",
      "multiplexor": "MuxSignal",
      "multiplex_values": [1]
    }
  ]
}
~~~

**Behavior**:
- When `MuxSignal == 0`, only `Signal_Mux0` is extracted
- When `MuxSignal == 1`, only `Signal_Mux1` is extracted
- Attempting to extract a signal that's not present returns an error
- Multiplexor signal must be defined in the same message and have `"presence": "always"`

**Implementation**: See [DESIGN.md](DESIGN.md) for the Agda module structure. The multiplexor logic is in the CAN signal extraction module; signal presence types are in the DBC types module.

---

### ValidateDBC

Validate a DBC definition for structural correctness. Returns all issues found (not just the first). Does not modify client state.

**Request**:
~~~json
{
  "type": "command",
  "command": "validateDBC",
  "dbc": { ... }
}
~~~

**Response**:
~~~json
{
  "status": "validation",
  "has_errors": true,
  "issues": [
    {"severity": "error", "code": "signal_overlap", "detail": "..."},
    {"severity": "warning", "code": "empty_message", "detail": "..."}
  ]
}
~~~

**Fields**:
- `dbc`: Complete DBC definition (same schema as `parseDBC`)
- Response `has_errors`: true if any issue has severity "error"
- Response `issues`: Array of validation issues

**Issue Codes**:
- **Error**: `duplicate_message_id`, `duplicate_signal_name`, `factor_zero`, `multiplexor_not_found`, `multiplexor_cycle`, `signal_exceeds_dlc`, `signal_overlap`, `bit_length_zero`
- **Warning**: `global_name_collision`, `min_exceeds_max`, `duplicate_message_name`, `offset_scale_range`, `empty_message`, `start_bit_out_of_range`, `bit_length_excessive`, `multiplexor_non_unit_scaling`, `duplicate_attribute_name`, `unknown_comment_target`, `unknown_message_sender`, `unknown_signal_receiver`, `unknown_value_description_target`, `multi_value_mux_selector`, `mux_master_incoherent`

The last two warning codes mirror the [FormatDBCText](#formatdbctext) round-trip checker's diagnostics, driven by the same kernel deciders: the DBC loads and streams fine, but cannot be expressed as round-tripping `.dbc` text — `formatDBCText` would refuse it. Like every warning, they never block a load (`has_errors` stays `false` when only warnings are present).

**State Requirements**: Does NOT require `parseDBC`. Does NOT modify client state (read-only probe).

---

### FormatDBCText

Render a DBC definition (JSON wire shape) back to `.dbc` file text via the verified Agda formatter — the text-level inverse of `parseDBCText`.

**Always strict.** `formatDBCText` returns text **only** when that text provably re-parses to the exact input DBC — `parseDBCText(formatDBCText(d).text)` reproduces `d`. There is no lenient/best-effort mode and no `strict` flag: a flag would imply you might sometimes want text that does *not* round-trip, which contradicts the command's whole purpose (never emit silently-lossy output). A DBC that cannot be expressed as round-tripping `.dbc` text — for example a signal multiplexed on **multiple** selector values, which the JSON model admits but the `.dbc` grammar cannot encode — is **refused** with a typed error rather than emitting text that would quietly lose information. The emitted-text round-trip guarantee is machine-checked (`formatDBCTextResult-sound` in `Aletheia.Protocol.Handlers.Properties.FormatDBCText`), not merely asserted.

**Request**:
~~~json
{
  "type": "command",
  "command": "formatDBCText",
  "dbc": { ... }
}
~~~

**Response** (Success — the DBC round-trips):
~~~json
{
  "status": "success",
  "text": "VERSION \"\"\n\nBO_ 256 Engine: 8 ECU\n ...",
  "issues": [
    {"severity": "warning", "code": "multi_value_mux_selector", "detail": "..."}
  ]
}
~~~

**Response** (Refusal — the DBC does not round-trip):
~~~json
{
  "status": "error",
  "code": "handler_text_roundtrip_failed",
  "message": "FormatDBCText: text round-trip failed: ...",
  "has_errors": true,
  "issues": [
    {"severity": "error", "code": "text_roundtrip_divergence", "detail": "re-parsing the emitted text does not reproduce the input DBC"},
    {"severity": "warning", "code": "multi_value_mux_selector", "detail": "..."}
  ]
}
~~~

**Fields**:
- `dbc`: Complete DBC definition (same schema as `parseDBC` input); absent → `route_missing_dbc_field`.
- Success `text`: the `.dbc` file image (a string).
- Success `issues`: **warning-severity** round-trip diagnostics (`wfTextIssues`). This list MAY be non-empty even on a successful round-trip — a warning flags a construct *outside the proven well-formed-text envelope* that nonetheless round-tripped; it is advisory, never a failure.
- Refusal `issues`: led by the error-severity `text_roundtrip_divergence` (the handler prepends it on every refusal), followed by the same warning diagnostics. `has_errors` is `true`.

The refusal envelope shares the `{severity, code, detail}` element shape, the `has_errors` flag, and the one-issue-decoder contract with the `handler_validation_failed` envelope (see [§ Wire shape](#wire-shape)) — a binding decodes both with the same issue decoder.

**Round-trip issue codes** (the codes this command's checker introduces; all severity **warning** except `text_roundtrip_divergence`). They are documented separately from the structural-validation codes under [ValidateDBC](#validatedbc), with two shared codes: `multi_value_mux_selector` and `mux_master_incoherent` are also emitted by `validateDBC` and the DBC-loading routes as warning-class mirrors driven by the same kernel deciders (a shape that loads cleanly but cannot round-trip to `.dbc` text is named without calling `formatDBCText`); the remaining codes are emitted by `formatDBCText` only:

| Code | Severity | Meaning |
|---|---|---|
| `text_roundtrip_divergence` | error | The emitted `.dbc` text does not re-parse to the input DBC — the refusal marker, prepended on every refusal |
| `multi_value_mux_selector` | warning | A signal is multiplexed on more than one selector value — expressible in JSON, not in the `.dbc` `SG_` grammar |
| `mux_master_incoherent` | warning | A multiplexed message's multiplexor master signal is missing or inconsistent |
| `unknown_attribute_name` | warning | A `BA_` attribute value references a name never declared via `BA_DEF_` |
| `attribute_value_type_mismatch` | warning | An attribute value does not fit its declared `BA_DEF_` type |
| `attribute_enum_empty` | warning | An `ENUM` attribute type declares no labels |
| `attribute_enum_default_unstable` | warning | An `ENUM` attribute's `BA_DEF_DEF_` default does not resolve to a stable label |

**State Requirements**: Does NOT require `parseDBC`. Does NOT modify client state (read-only) — pass any DBC value (typically from `parseDBCText`, `formatDBC`, or the JSON converters).

Every binding surfaces this as `format_dbc_text(dbc)`: `text` + `issues` on success, and a typed round-trip-refusal error (Python `TextRoundTripFailedError`, Go `*TextRoundTripFailedError`, C++ `AletheiaError` with `ErrorKind::TextRoundtrip`, Rust `Error::TextRoundtripFailed`) carrying the diverging issue list — see the `dbc_text_roundtrip_check` row in [FEATURE_MATRIX.yaml](../FEATURE_MATRIX.yaml).

---

### SetProperties

Define LTL properties to check against the frame stream.

**Request**:
~~~json
{
  "type": "command",
  "command": "setProperties",
  "properties": [
    {
      "operator": "always",
      "formula": {
        "operator": "atomic",
        "predicate": {
          "predicate": "lessThan",
          "signal": "Speed",
          "value": 250
        }
      }
    }
  ]
}
~~~

**Response** (Success):
~~~json
{
  "status": "success",
  "message": "Properties set successfully"
}
~~~

**Response** (Error):
~~~json
{
  "status": "error",
  "message": "Signal 'Speed' not found in DBC"
}
~~~

**State Requirements**: Must be in `ReadyToStream` state (after parseDBC)
**State Transition**: `ReadyToStream` → `ReadyToStream` (idempotent)

See [LTL Property Format](#ltl-property-format) section below for complete schema.

---

## Binary Entry Points

The stream and its frames go through C entry points that take their input as C values, never as JSON; `aletheia.h` fixes the layout of every structure they read. A JSON-answering entry returns a string the caller frees with `aletheia_free_str()`; a binary-output entry fills a `struct aletheia_buffer`. Every binding drives the stream through these entries.

**The kernel parses every frame.** `Aletheia.CAN.Frame.Parse` reads a frame's fields as the caller passed them and refuses one that breaks a rule before any state changes, checking them in this order and the payload byte by byte, so the first rule broken is the one reported:

| Rule | Code |
|---|---|
| A standard identifier is below 2048, an extended one below 2²⁹ | `parse_std_can_id_out_of_range` / `parse_ext_can_id_out_of_range` |
| The DLC is at most 15 | `parse_dlc_code_out_of_range` |
| `data_len` is the DLC's byte count: the code itself up to 8, then 12, 16, 20, 24, 32, 48, 64 | `parse_payload_length_mismatch` |
| Every payload byte is below 256 | `parse_payload_byte_out_of_range` |

`data_len` is a `uint8_t`, so no payload over 255 bytes reaches the kernel. Every binding checks a payload against its DLC before calling, so these codes reach only a caller of the C entries themselves.

### aletheia_start_stream and aletheia_end_stream

~~~c
char *aletheia_start_stream(void *state);
char *aletheia_end_stream(void *state);
~~~

`aletheia_start_stream()` moves a session with a loaded DBC from `ReadyToStream` to `Streaming`:

~~~json
{"status": "success", "message": "Streaming started successfully"}
~~~

Without a DBC it answers `handler_no_dbc`, and on a stream already started `handler_already_streaming`.

`aletheia_end_stream()` closes the stream, returning the session to `ReadyToStream` (it can stream again), and answers each property's final verdict:

~~~json
{"status": "complete", "results": [{"type": "property", "status": "holds", "property_index": 0}], "warnings": []}
~~~

`warnings` carries the non-fatal end-of-stream diagnostics described under [End-of-stream Warnings](#end-of-stream-warnings), and is present, empty, when none fired. Outside a stream it answers `handler_not_streaming`.

### aletheia_send_frame

~~~c
char *aletheia_send_frame(void *state, const struct aletheia_frame *frame);
~~~

The streaming hot path for data frames. **Frame fields** (`struct aletheia_frame`, every one read; a NULL frame is refused):

- `timestamp`: microseconds, non-decreasing across the stream's events (an equal timestamp is accepted).
- `can_id`, `extended`: the identifier, 11-bit when `extended` is 0, 29-bit otherwise; it selects the DBC message the signals are read with.
- `dlc`, `data`, `data_len`: the DLC code and its payload, held to the rules above.
- `brs_present` / `brs_value`: the CAN-FD Bit Rate Switch (ISO 11898-1:2015 §10.4.2), true when the data phase ran at the higher bit rate. `*_present = 0` means the bit is absent (a CAN 2.0B frame); otherwise the bit is `*_value != 0`.
- `esi_present` / `esi_value`: the CAN-FD Error State Indicator (§10.4.3), true when the transmitter is error-passive, encoded as BRS.

The kernel does not consume BRS or ESI: LTL atomic predicates are signal-level (see the design comment in [Aletheia.Trace.CANTrace](../../src/Aletheia/Trace/CANTrace.agda)). Bindings keep them as pass-through metadata on their frame type, and no response echoes them.

**Response** (no property decided at this frame):

~~~json
{"status": "ack"}
~~~

**Response** (property batch):

~~~json
{"type": "property_batch", "results": [{"type": "property", "status": "fails", "property_index": 0, "timestamp": 2000, "reason": "Atomic: predicate failed"}]}
~~~

A frame produces no event (answered `ack`) or one or more in `results`: the properties that completed at this frame first, in property order, then at most one violation, which ends the frame's evaluation and comes last. An empty `results` never occurs.

**Refusals**: no DBC loaded, `handler_no_dbc`; a DBC but no stream, `handler_stream_not_started`; a timestamp below the previous event's, `handler_non_monotonic_timestamp`; a frame breaking a rule above, its `parse_*` code.

**Why binary?** It removes JSON serialization and parsing from the streaming hot path: 4.3x the throughput of a JSON route for CAN 2.0B, 9.1x for CAN-FD (see [BENCHMARKS.md](../development/BENCHMARKS.md#canonical-results) for the methodology and per-language numbers).

### aletheia_send_error and aletheia_send_remote

Error frames and remote frames are non-data trace events. Both take the same `struct aletheia_frame`: a remote frame reads its `timestamp`, `can_id` and `extended`, an error frame its `timestamp` alone.

~~~c
char *aletheia_send_error(void *state, const struct aletheia_frame *frame);
char *aletheia_send_remote(void *state, const struct aletheia_frame *frame);
~~~

#### Trace event taxonomy

The Agda core models a CAN trace as a sequence of `TraceEvent` values (see `Aletheia/Trace/CANTrace.agda`):

| Constructor | Carries | FFI entry point | Purpose |
|---|---|---|---|
| `Data tf` | a `TimedFrame`: timestamp, identifier, DLC, payload, BRS / ESI | `aletheia_send_frame` | Normal data frame, drives signal extraction. |
| `Error ts` | timestamp only | `aletheia_send_error` | Bus-error event (CAN error frame on the wire). |
| `Remote ts canId` | timestamp + identifier, no payload | `aletheia_send_remote` | Remote transmission request (RTR). |

#### What each event does

In a stream, the three event kinds share one clock: timestamps are non-decreasing across all of them, and a timestamp below the previous event's, whichever entry delivered it, is refused with `handler_non_monotonic_timestamp`. Mixing `aletheia_send_frame` and `aletheia_send_error` does not reset the clock.

| Step | `send_frame` | `send_error` | `send_remote` |
|---|---|---|---|
| 1. Parse the frame (rules above) | ✅ identifier, DLC, payload | — | ✅ identifier |
| 2. Extract signals from payload | ✅ | — | — |
| 3. Update signal cache | ✅ | — | — |
| 4. Advance LTL clock by `ts` | ✅ | ✅ | ✅ |
| 5. Re-evaluate active properties | ✅ | ✅ (no signal change, but metric windows may expire) | ✅ |
| 6. Emit verdict if a property terminates | ✅ | ✅ | ✅ |

The key consequence of step 5: **error and remote frames can finalize a metric `eventually` window or trigger a `between(...)` deadline expiry**, even though they carry no signal updates. This matches LTLf semantics: the clock advances, so any property whose window closes between events resolves on the next timestamp regardless of the event kind.

Outside a stream, with or without a DBC, an error or remote frame is answered `ack` and leaves the session as it was, its clock included; a data frame is refused there, as above.

#### Response shape

The response shape is identical to `aletheia_send_frame`: an `ack` if no property terminated, or a property batch if one did. The binding wrappers `send_error()` / `send_remote()` (Python, C++, Go, Rust) parse the same response types they use for data frames.

### aletheia_extract_signals

~~~c
char *aletheia_extract_signals(void *state, const struct aletheia_frame *frame);
~~~

Extracts every signal of a frame's message against the loaded DBC, without a stream and without changing the session. Reads the frame's `can_id`, `extended`, `dlc`, `data` and `data_len`.

~~~json
{"status": "success", "values": [{"name": "Speed", "value": 100}], "errors": [], "absent": []}
~~~

- `values`: the signals extracted, with their physical values.
- `errors`: the signals whose extraction failed, each with its reason.
- `absent`: the multiplexed signals this frame's multiplexor value does not select.

**Refusals**: no DBC loaded, `handler_no_dbc`; a frame breaking a rule above, its `parse_*` code.

### aletheia_format_dbc

~~~c
char *aletheia_format_dbc(void *state);
~~~

Answers the loaded DBC as JSON, in the schema `parseDBC` takes, without changing the session:

~~~json
{"status": "success", "dbc": {"version": "1.0", "messages": [...]}}
~~~

Without a DBC it answers `handler_no_dbc`. The distinct [`formatDBCText`](#formatdbctext) command renders a DBC as `.dbc` text.

### aletheia_build_frame_bin, aletheia_update_frame_bin and aletheia_extract_signals_bin

The binary-output entries answer 0 on success and 1 on failure, with their result in a `struct aletheia_buffer` (see `aletheia.h`): a build or an update writes the frame's bytes into the caller's buffer, an extraction allocates the packed layout `Aletheia/Main/Binary.agda` documents.

Signal values for a build or an update cross as three parallel arrays (`struct aletheia_signal_values`: indices, numerators, denominators); the kernel builds each value as an exact rational in lowest terms and refuses a denominator that is not positive with `parse_non_positive_denominator` (and arrays of unequal length with `parse_signal_array_length_mismatch`, which the C structure, carrying one count, cannot express).

On failure the buffer's `err` is the JSON error envelope every other entry answers with, freed with `aletheia_free_str()`:

~~~json
{"status": "error", "code": "parse_non_positive_denominator", "message": "non-positive denominator 0"}
~~~

The code is the kernel's refusal, or `ffi_validation_error` for a NULL frame or signal values, or a buffer smaller than the frame the kernel built.

---

## Response Types

### Success Response
~~~json
{
  "status": "success",
  "message": "Operation completed"
}
~~~

### Error Response
~~~json
{
  "status": "error",
  "message": "Descriptive error message"
}
~~~

### Acknowledgment Response
~~~json
{
  "status": "ack"
}
~~~
Used for data frames when no violation is detected.

### Property Batch Response
~~~json
{
  "type": "property_batch",
  "results": [
    {"type": "property", "status": "holds", "property_index": {"numerator": 0, "denominator": 1}},
    {"type": "property", "status": "fails", "property_index": {"numerator": 1, "denominator": 1}, "timestamp": {"numerator": 300, "denominator": 1}, "reason": "Always violated"}
  ]
}
~~~

A streaming frame may produce zero events (returns `{"status": "ack"}`)
or one-or-more events in `results` in source-order: mid-stream
Satisfactions first (a property that completed at this frame and was
dropped from the active set), optionally followed by a terminal
Violation (the iteration halt).  A frame contains at most one Violation;
if present it is the last entry.  Empty `results` is unreachable.

**Inner entry fields** (each `results[i]`):
- `type`: always `"property"`
- `status`: `"fails"`, `"holds"`, or `"unresolved"`
- `property_index`: index of the property (rational)
- `timestamp`: timestamp of the violation (rational, only present when `status == "fails"`)
- `reason`: human-readable explanation (only present when `status == "fails"`)

### Complete Response
~~~json
{
  "status": "complete",
  "results": [
    {"type": "property", "status": "holds", "property_index": {"numerator": 0, "denominator": 1}},
    {"type": "property", "status": "fails", "property_index": {"numerator": 1, "denominator": 1}, "timestamp": {"numerator": 4523, "denominator": 1}, "reason": "Always violated"}
  ],
  "warnings": [
    {"kind": "uncached_atom", "property_index": 2, "detail": "Speed"}
  ]
}
~~~
Returned when streaming ends. The `results` array contains per-property finalization verdicts; the `warnings` array carries non-fatal end-of-stream diagnostics (see [§ End-of-stream Warnings](#end-of-stream-warnings)).

#### End-of-stream Warnings

The `warnings` field on the `Complete` response is a (possibly empty) list of `Warning` records emitted by the verified kernel during end-of-stream finalization. Each warning ratifies — never replaces — a per-property verdict in `results` by providing diagnostic context.

**Wire shape** (every binding decodes the same JSON):

| Field | Type | Description |
|---|---|---|
| `kind` | string | Enumerated warning class. Currently `"uncached_atom"`; the kernel may add new kinds additively. Bindings MUST accept unknown `kind` values without rejecting the response. |
| `property_index` | integer | Zero-based index into the registered property set; identifies which property the warning relates to. |
| `detail` | string | Free-form diagnostic detail. Schema depends on `kind`. For `uncached_atom`, the unobserved signal name. |

**Defined warning kinds**:

- **`uncached_atom`** — end-of-stream finalization found at least one atom in the property whose target signal was never observed during the stream. The property's verdict remains the verdict the kernel computed (typically `Unresolved`); the warning attaches the signal name so operators can identify the missing data source. `detail` carries the signal name. Soundness rationale: the existing verdict is emitted unchanged — warnings are additive diagnostic context, they do not alter the verdict. See [`Aletheia.Protocol.Adequacy.StreamingWarm`](../../src/Aletheia/Protocol/Adequacy/StreamingWarm.agda) for the underlying adequacy theorem.

**Evolution rule (binding contract)**:

Adding a new `kind` requires a coordinated change:

1. Extend the Agda kernel's `WarningKind` ADT and the JSON serializer in `Aletheia.Protocol.ResponseFormat`.
2. Add a new `endstream.<kind>` row to [`docs/LOG_EVENTS.yaml`](../LOG_EVENTS.yaml).
3. Add a matching log event emit site in all four bindings' `end_stream` / `EndStream` implementations (level: `warn`).
4. Add a per-binding parity test that exercises the new kind.
5. Add a `#### `endstream.<kind>`` heading to [`docs/operations/RUNBOOK.md`](../operations/RUNBOOK.md).
6. Update this section's table of defined kinds.
7. Add a CHANGELOG entry under `Added` per Public API stability discipline.

Removing or renaming a `kind` is a breaking wire change (downstream collectors may be filtering on the literal name) and is governed by the CHANGELOG `Removed` discipline.

**Logging mirror**: Per-binding `end_stream` implementations re-emit each warning as a `endstream.<kind>` structured log event (level `warn`) with `property_index` and `detail` fields, in addition to the aggregate `stream.ended` event's `numWarnings` count. The per-warning events let operators grep for specific properties. See [`docs/LOG_EVENTS.yaml`](../LOG_EVENTS.yaml) and the per-binding parity tests for the canonical contract.

---

## LTL Property Format

### Signal Predicates (Atomic)

#### Equals
~~~json
{
  "predicate": "equals",
  "signal": "Speed",
  "value": 100
}
~~~

#### LessThan
~~~json
{
  "predicate": "lessThan",
  "signal": "Speed",
  "value": 250
}
~~~

#### GreaterThan
~~~json
{
  "predicate": "greaterThan",
  "signal": "RPM",
  "value": 0
}
~~~

#### Between
~~~json
{
  "predicate": "between",
  "signal": "Temperature",
  "min": 60,
  "max": 90
}
~~~

#### LessThanOrEqual
~~~json
{
  "predicate": "lessThanOrEqual",
  "signal": "Speed",
  "value": 250
}
~~~

#### GreaterThanOrEqual
~~~json
{
  "predicate": "greaterThanOrEqual",
  "signal": "RPM",
  "value": 800
}
~~~

#### ChangedBy
~~~json
{
  "predicate": "changedBy",
  "signal": "Speed",
  "delta": -10
}
~~~
Directional change detection. Positive delta: `curr - prev >= delta` (increased by at least delta). Negative delta: `curr - prev <= delta` (decreased by at least |delta|).

#### StableWithin
~~~json
{
  "predicate": "stableWithin",
  "signal": "Temperature",
  "tolerance": 2.0
}
~~~
Magnitude tolerance: `|curr - prev| <= tolerance`. Tests that a signal's value stayed within tolerance of its previous value.

---

### LTL Temporal Operators

#### Atomic (wraps a signal predicate)
~~~json
{
  "operator": "atomic",
  "predicate": {
    "predicate": "equals",
    "signal": "Speed",
    "value": 100
  }
}
~~~

#### Not
~~~json
{
  "operator": "not",
  "formula": {...}
}
~~~

#### And
~~~json
{
  "operator": "and",
  "left": {...},
  "right": {...}
}
~~~

#### Or
~~~json
{
  "operator": "or",
  "left": {...},
  "right": {...}
}
~~~

#### Next
~~~json
{
  "operator": "next",
  "formula": {...}
}
~~~
Property must hold in the next frame. Fails at end of stream (no successor).

#### Weak Next
~~~json
{
  "operator": "weakNext",
  "formula": {...}
}
~~~
Property must hold in the next frame, or holds vacuously at end of stream
(no successor). Use for "if X then next Y" patterns where X may be true on
the final frame, where strong Next would report a violation the trace's end
causes rather than the property.

#### Always (Globally)
~~~json
{
  "operator": "always",
  "formula": {...}
}
~~~
Property must hold for all frames in the trace.

#### Eventually (Finally)
~~~json
{
  "operator": "eventually",
  "formula": {...}
}
~~~
Property must hold at some point in the trace.

#### Until
~~~json
{
  "operator": "until",
  "left": {...},
  "right": {...}
}
~~~
`left` must hold until `right` becomes true.

#### Release
~~~json
{
  "operator": "release",
  "left": {...},
  "right": {...}
}
~~~
Dual of Until: `right` must hold until `left` releases it (or `right` holds forever).

#### MetricEventually (Bounded Eventually)
~~~json
{
  "operator": "metricEventually",
  "timebound": 1000,
  "formula": {...}
}
~~~
Property must hold within `timebound` microseconds.

#### MetricAlways (Bounded Always)
~~~json
{
  "operator": "metricAlways",
  "timebound": 5000,
  "formula": {...}
}
~~~
Property must hold for the next `timebound` microseconds.

#### MetricUntil (Bounded Until)
~~~json
{
  "operator": "metricUntil",
  "timebound": 2000,
  "left": {...},
  "right": {...}
}
~~~
`left` must hold until `right` becomes true, within `timebound` microseconds.

#### MetricRelease (Bounded Release)
~~~json
{
  "operator": "metricRelease",
  "timebound": 2000,
  "left": {...},
  "right": {...}
}
~~~
Bounded dual of Until: `right` must hold until `left` releases it, within `timebound` microseconds.

---

### Streaming Semantics: Soundness vs. Completeness

Aletheia's incremental evaluator is **sound** but not **complete** for liveness
operators (`Eventually`, `Until`, and their metric variants). The distinction
matters when interpreting a `"complete"` response:

- **Sound** — every definite verdict is correct. If the stream ends with a
  property reported as `Satisfied` or `Violated`, that verdict is
  provably correct relative to the observed trace. This is formally proven
  in `LTL/Adequacy.agda`, lifted to the production simplify/stepL loop by
  `LTL/Adequacy/Pipeline.agda` (`pipeline-adequate`), and discharged for
  the signal-cache premise by `Protocol/Adequacy/StreamingWarm.agda`
  (`streaming-warms-cache`) **provided** the trace satisfies
  `AllObserved dbc σ atoms` — i.e., every predicate's target signal is
  extracted from at least one frame in the trace. The FFI runtime does
  not check `AllObserved`; it is a user obligation on the input trace.
  Traces that omit a property's target signal may still report `Unknown`
  (three-valued finalization) rather than a definite verdict, which
  remains sound but not complete.
- **Not complete** — some verdicts may remain `Unknown` at end-of-stream
  even when the prefix already determined the truth value. Example:
  `Eventually Speed > 0` reports `Unknown` if the stream ends before the
  condition is seen, but could theoretically be proven `Violated` with more
  sophisticated lookahead. Aletheia does not perform such lookahead —
  it reports `Unknown` and leaves the interpretation to the caller.

**Operators with bounded completeness** — `MetricEventually`, `MetricUntil`
and their `MetricAlways`/`MetricRelease` duals resolve to a definite verdict
once their `timebound` window has fully elapsed. Unbounded `Eventually`/
`Until` can only resolve definitely when the witness is observed; otherwise
they remain `Unknown`.

**Practical guidance** — prefer metric operators with explicit timebounds
when you need a guaranteed definite verdict. Use unbounded `Eventually`/
`Until` only when `Unknown` at end-of-stream is an acceptable outcome.

---

### Complete Example

**Property**: "Speed must always be less than 250 km/h"

~~~json
{
  "operator": "always",
  "formula": {
    "operator": "atomic",
    "predicate": {
      "predicate": "lessThan",
      "signal": "Speed",
      "value": 250
    }
  }
}
~~~

---

## Rational Number Encoding

Rational numbers are represented in two formats:

### 1. Decimal Format (Input)
~~~json
{"value": 0.25}
~~~
Accepted in input, converted to rational internally.

### 2. Object Format (Output)
~~~json
{"numerator": 1, "denominator": 4}
~~~
Used in responses for exact representation.

**Why Two Formats?**
- Decimal format is convenient for users (e.g., `"factor": 0.1`)
- Object format preserves exact values (e.g., 1/3 has no finite decimal)
- Parser accepts both, formatter outputs object format

**Examples**:
- `0.25` → `{"numerator": 1, "denominator": 4}`
- `1.5` → `{"numerator": 3, "denominator": 2}`
- `100` → `{"numerator": 100, "denominator": 1}`

**Note**: The JSON format exposes the actual denominator for clarity, even though the internal representation may differ.

---

## Example Session

### 1. Parse DBC
~~~json
>>> {"type": "command", "command": "parseDBC", "dbc": {...}}
<<< {"status": "success", "message": "DBC parsed successfully"}
~~~

### 2. Set Properties
~~~json
>>> {"type": "command", "command": "setProperties", "properties": [{...}]}
<<< {"status": "success", "message": "Properties set successfully"}
~~~

### 3. Start Streaming
~~~
>>> aletheia_start_stream(state)
<<< {"status": "success", "message": "Streaming started"}
~~~

### 4. Send Data Frames (via `aletheia_send_frame`)

High-throughput streaming hot path. Each call passes a `struct aletheia_frame` with `can_id` 256, `extended` 0, `dlc` 8 and `data_len` 8; its BRS / ESI fields, left zero, encode absent CAN-FD metadata:
~~~
>>> aletheia_send_frame(state, &{timestamp: 100, data: [0xE8,0x03,0,0,0,0,0,0], ...})
<<< {"status": "ack"}

>>> aletheia_send_frame(state, &{timestamp: 200, data: [0xD0,0x07,0,0,0,0,0,0], ...})
<<< {"status": "ack"}

>>> aletheia_send_frame(state, &{timestamp: 300, data: [0x28,0x0A,0,0,0,0,0,0], ...})
<<< {"type": "property_batch", "results": [{"type": "property", "status": "fails", "property_index": {"numerator": 0, "denominator": 1}, "timestamp": {"numerator": 300, "denominator": 1}, "reason": "Always violated"}]}
~~~

### 5. End Streaming
~~~
>>> aletheia_end_stream(state)
<<< {"status": "complete", "results": [{"type": "property", "status": "holds", "property_index": {"numerator": 0, "denominator": 1}}, {"type": "property", "status": "fails", "property_index": {"numerator": 1, "denominator": 1}, "timestamp": {"numerator": 300, "denominator": 1}, "reason": "Always violated"}]}
~~~

---

## Limits

Every parser at a trust boundary enforces explicit upper bounds on adversarial inputs. Rejection over the bound is a typed `InputBoundExceeded` error carrying the offending kind, the observed value, and the canonical limit it crossed; never a crash, never an OOM, never a stalled stream.

The single source of truth is the Agda module `Aletheia.Limits` (`src/Aletheia/Limits.agda`); each binding mirrors the same constants in its native error-type surface.

### Bound constants

| Bound | Limit | Kind code |
|---|---:|---|
| Total DBC text input | 64 MiB (67,108,864 bytes) | `input_length_bytes` |
| Total JSON input (FFI boundary) | 64 MiB (67,108,864 bytes) | `input_length_bytes` |
| JSON nesting depth | 64 | `nesting_depth` |
| Messages per DBC file | 10,000 | `array_cardinality` |
| Signals per single message | 1,024 | `array_cardinality` |
| Attribute defs / assignments per file | 10,000 | `array_cardinality` |
| Value descriptions per file (`VAL_` + `VAL_TABLE_`) | 1,000,000 | `array_cardinality` |
| Comments per DBC file (`CM_`) | 10,000 | `array_cardinality` |
| Nodes per DBC file (`BU_`) | 10,000 | `array_cardinality` |
| Value tables per DBC file (`VAL_TABLE_` definitions) | 10,000 | `array_cardinality` |
| LTL atoms per property | 1,024 | `atom_count` |
| Properties per `setProperties` call | 1,024 | `property_count` |
| DBC identifier length | 128 chars | `identifier_length` |
| Quoted-string body length | 64 KiB (65,536 bytes) | `string_length` |
| Rational components of any JSON number (\|numerator\| and denominator of the exact rational it denotes, reduced) | 9,223,372,036,854,775,807 (2⁶³ − 1) | `rational_component_magnitude` |

The rational-component bound is measured on the parsed tree like the nesting-depth bound (reduction only shrinks component magnitudes, so a bounded submitted literal stays bounded). It pins the JSON wire to the same signed 64-bit range the binary FFI's rational slots and the typed decimal path (`aletheia_parse_decimal`) already enforce — one Int64 bound on every wire, so a bare JSON integer cannot smuggle a component the binary wire cannot represent. The limit is symmetric in magnitude: numerator −2⁶³ is refused even though a two's-complement slot could carry it, keeping the structured `observed` / `limit` pair a plain magnitude comparison.

A frame has no bound kind: `data_len` is a `uint8_t`, and the kernel refuses any payload whose length is not its DLC's byte count with `parse_payload_length_mismatch` (see [Binary Entry Points](#binary-entry-points)).

### Wire shape

`InputBoundExceeded` errors surface as the standard `{"status": "error", ...}` envelope with the consolidated code `input_bound_exceeded`. The `bound_kind` field in the structured payload discriminates which kind of bound was crossed, matching the `BoundKind` enum in `Aletheia.Limits`:

| Code | bound_kind values |
|---|---|
| `input_bound_exceeded` | `input_length_bytes` / `nesting_depth` / `array_cardinality` / `identifier_length` / `string_length` / `atom_count` / `property_count` / `rational_component_magnitude` |

The `message` field embeds the kind label, observed value, and limit; the structured `bound_kind` / `observed` / `limit` fields appear on the envelope alongside `code` and `message`. Example:

~~~
<<< {"status": "error", "code": "input_bound_exceeded", "message": "input length (bytes) 134217728 exceeds limit 67108864", "bound_kind": "input_length_bytes", "observed": 134217728, "limit": 67108864}
~~~

For the post-parse DBC bounds (`array_cardinality` and `string_length`), all three DBC commands — `parseDBC`, `parseDBCText`, and `validateDBC` — run one shared cascade (kernel `Aletheia.Protocol.Handlers.LoadDBC.checkDBCBounds`), so the `message` names the offending field alongside the command context, e.g. `ParseDBCText: version string: string length 65546 exceeds limit 65536`. `validateDBC` runs the same cascade — an over-cardinality / over-length DBC is rejected with `input_bound_exceeded` *before* validation runs (the structured `bound_kind` / `observed` / `limit` fields are identical across all three routes, so a binding decodes it with the same typed handler it uses for the load routes).

`handler_validation_failed` errors (a `parseDBC` / `parseDBCText` rejected because the DBC has error-level validation issues) carry the **full structured issue list** on the envelope — errors *and* warnings, in the same `{severity, code, detail}` element shape as the `validation` response, plus the same `has_errors` flag (trivially `true` on this path; included so both payloads decode with one issue decoder). The `message` field flattens only the error-level details. Example:

~~~
<<< {"status": "error", "code": "handler_validation_failed", "message": "ParseDBCText: validation failed: Message 'M': duplicate signal name 'S'", "has_errors": true, "issues": [{"severity": "error", "code": "duplicate_signal_name", "detail": "Message 'M': duplicate signal name 'S'"}, {"severity": "warning", "code": "offset_scale_range", "detail": "..."}]}
~~~

DBC text parse errors carry **byte-exact failure positions** on the envelope. The parser tracks a *furthest-failure watermark*: the deepest position any parse attempt reached (`<|>` alternatives merge their failed arms' depths; `many` keeps the depth of the element attempt it swallowed), so the reported byte is the first character no grammar rule could accept — not merely the start of the offending statement.

- `dbc_text_parse_failure` exposes structured `line` / `column` (the watermark).
- `dbc_text_trailing_input` exposes `line` / `column` (the watermark, inside the first unparseable statement) **plus** `statement_line` / `statement_column` (where that statement starts — the first unconsumed byte).
- `dispatch_invalid_json` exposes `line` / `column` (the JSON parser shares the same combinators and watermark).

### Two-layer enforcement

Per AGENTS.md universal rule "Adversarial-input bounds at parser surfaces", bounds are enforced **twice**:

1. **Agda kernel** — definitive. `Aletheia.Limits.max-*` constants are checked at the parser entry inside the verified core; the typed `InputBoundExceeded` error flows out via the protocol `Response`.
2. **Per-binding FFI entry** — short-circuit. Python `aletheia.InputBoundExceededError`, Go `*aletheia.InputBoundExceededError`, and C++ `aletheia::InputBoundExceededError` reject oversize inputs before marshaling them across the FFI boundary, so a 100 MB JSON does not allocate buffers in the binding before being rejected.

The two layers must agree on the numeric limits; cross-binding regression tests verify this.

### Updating bounds

Bounds are intentionally generous (commercial automotive DBCs are 1-10 MiB, ~6× headroom). If your inputs legitimately exceed a bound:

1. Surface the bound and the legitimate input size in an issue or PR.
2. Update `Aletheia.Limits.max-*` (single source of truth).
3. Mirror the constant in each binding's reject-on-FFI-entry guard.
4. Update this table.

---

## Error Handling

### Common Errors

**Invalid JSON**:
~~~
<<< {"status": "error", "message": "Failed to parse JSON: unexpected token"}
~~~

**Missing Required Field**:
~~~
<<< {"status": "error", "message": "Missing required field: 'command'"}
~~~

**Invalid State Transition**:
~~~
<<< {"status": "error", "code": "handler_no_dbc", "message": "StartStream: DBC not loaded"}
~~~

**Signal Not Found**:
~~~
<<< {"status": "error", "message": "Signal 'InvalidSignal' not found in DBC"}
~~~

**Message ID Not Found**:
~~~
<<< {"status": "error", "message": "Message ID 999 not found in DBC"}
~~~

### Error Code Reference

Every error response carries a stable `code` field (in addition to the human-readable `message`) drawn from the Agda source of truth `src/Aletheia/Error.agda`. Tooling should switch on `code`, not `message` — the message text is localised/expanded over time, the code is not.

Codes are grouped by domain: `parse_*` (JSON/DBC parsing), `extraction_*` (signal extraction), `frame_*` (frame building/update), `route_*` (command dispatch), `handler_*` (stream state machine), `dispatch_*` (top-level request routing), `dbc_text_*` (DBC text parse/format). When an error is wrapped (e.g., a `ParseError` surfaces through `WrappedParse` inside a `HandlerError`), the emitted `code` is the innermost code, not the wrapping layer — so `parse_missing_field` during `parseDBC` and during `setProperties` both surface as `parse_missing_field`.

#### Parse errors — malformed DBC or property JSON, or a binary entry's frame

| Code | Meaning | Likely cause / fix |
|---|---|---|
| `parse_missing_field` | Required JSON field absent | Check the schema in the relevant Command section above |
| `parse_invalid_byte_order` | Byte order string not `little_endian` or `big_endian` | Fix the signal `byteOrder` value |
| `parse_invalid_presence` | Presence string not `always` | Use `always` or switch to `multiplexor`/`multiplex_values` |
| `parse_non_integer_multiplex_value` | `multiplex_values` array contains a non-natural element | Every element must be a JSON natural number |
| `parse_missing_signed` | Signal `signed` field absent | Add `"signed": true` or `"signed": false` |
| `parse_invalid_signed` | `signed` value not `signed` or `unsigned` (legacy string form) | Use boolean `true`/`false` |
| `parse_not_an_object` | Array element expected to be an object | Messages/signals must be JSON objects |
| `parse_ext_can_id_out_of_range` | Extended CAN ID above 29-bit max | Must be `≤ 536870911` |
| `parse_std_can_id_out_of_range` | Standard CAN ID above 11-bit max | Must be `≤ 2047` |
| `parse_default_can_id_out_of_range` | CAN ID exceeds standard range, `extended` not set | Set `"extended": true` |
| `parse_invalid_dlc_bytes` | DLC byte count is not a valid CAN/CAN-FD length | DLC `0-15` only; values map to {0..8,12,16,20,24,32,48,64} |
| `parse_root_not_object` | Top-level JSON is not an object | Wrap the request in `{...}` |
| `parse_missing_signal_name` | Signal object has no `name` | Add `"name": "..."` |
| `parse_signal_bit_length_zero` | Signal `length` is zero | Must be `≥ 1` |
| `parse_signal_start_bit_exceeds_frame` | Signal `startBit` lies outside the message's frame capacity | Must be `< dlcToBytes(dlc) * 8` |
| `parse_signal_bit_length_exceeds_frame` | Signal `length` exceeds the message's frame capacity | Must be `≤ dlcToBytes(dlc) * 8` |
| `parse_signal_big_endian_overflow` | Big-endian signal's descending bit run extends past the end of the frame | The Motorola `startBit` names the MSB; `length` bits must fit below it within the frame |
| `parse_invalid_kind` | An enum-like string field carries an unrecognised value (`invalid <domain> kind '<value>'`) | Use one of the documented values for that field |
| `parse_non_terminating_rational` | A rational field is non-terminating in decimal (denominator has a prime factor outside {2, 5}) | Use a value representable as a terminating decimal |
| `parse_invalid_identifier` | String is not a valid DBC identifier (must start with a letter or `_`, then alphanumerics/`_`) | Fix the identifier name |
| `parse_non_natural_field` | A field is present but its value is not a JSON natural number | Supply a non-negative integer |
| `parse_dlc_code_out_of_range` | A binary entry's frame has a DLC above 15 | Encode the DLC as a code `0-15` |
| `parse_payload_length_mismatch` | A binary entry's frame has a `data_len` that is not its DLC's byte count | Send exactly `dlcToBytes(dlc)` bytes |
| `parse_payload_byte_out_of_range` | A binary entry's payload byte is 256 or above | Unreachable through `aletheia.h`'s `uint8_t` payload |
| `parse_non_positive_denominator` | A signal value for a build or an update has a zero or negative denominator | Give each value a positive denominator |
| `parse_signal_array_length_mismatch` | A build's or an update's signal-value arrays differ in length | Unreachable through `struct aletheia_signal_values`, which carries one count |

#### Extraction errors — signal extraction on a data frame

| Code | Meaning | Likely cause / fix |
|---|---|---|
| `extraction_mux_value_mismatch` | Multiplexor value in frame does not select this signal | Not an error in `extractAllSignals` — the signal appears in `absent`, not `errors` |
| `extraction_mux_signal_not_found` | Named multiplexor signal missing from message definition | DBC inconsistency — fix the DBC |
| `extraction_mux_chain_cycle` | Multiplexor chain exceeded recursion depth (cycle?) | Simplify or break the multiplexor chain |
| `extraction_mux_extraction_failed` | Failed to read the multiplexor signal's own bits | Check the multiplexor signal's `startBit`/`length` |
| `extraction_value_exceeds_wire_range` | The extracted exact value's reduced numerator or denominator exceeds the signed 64-bit range of the binary wire's rational slots, so the value cannot travel the wire (the FFI encoder reroutes the signal to `errors` instead of letting the value wrap silently) | Per-signal runtime condition, not a DBC defect — reduction alone can push a component over the range even when every DBC field and frame byte is in range; rescale the signal's `factor`/`offset` if the exact value must travel |

#### Frame errors — binary build/update paths (`aletheia_build_frame_bin` / `aletheia_update_frame_bin`)

| Code | Meaning | Likely cause / fix |
|---|---|---|
| `frame_signal_not_found` | Named signal not in the target message | Check the signal name against the DBC |
| `frame_signal_index_oob` | Internal signal index out of range | Indicates a DBC/runtime mismatch — rebuild |
| `frame_injection_failed` | Bit-packing failed for a signal | Usually means the value exceeds the signal's bit width |
| `frame_signals_overlap` | Two requested signals occupy overlapping bits | Edit only one signal per bit range, or fix the DBC |
| `frame_can_id_not_found` | `canId` not present in loaded DBC | Re-check the CAN ID against the DBC |
| `frame_can_id_mismatch` | Request `canId` does not match the frame being updated | For the binary update path, the existing frame's ID must match |
| `frame_signal_value_out_of_bounds` | Physical value outside the signal's `[minimum, maximum]` | Clip at the caller, or loosen the DBC bounds |

#### Route errors — command dispatch

| Code | Meaning | Likely cause / fix |
|---|---|---|
| `route_missing_field` | Command-level required field missing | See the specific command's fields |
| `route_unknown_command` | `command` value not recognised | See the Commands section for the valid commands |
| `route_missing_command_field` | Request has no `command` field | Add `"command": "..."` |
| `route_missing_dbc_field` | `parseDBC`/`validateDBC` missing `dbc` field | Add the `dbc` object |
| `route_missing_props_field` | `setProperties` missing `properties` field | Add `"properties": [...]` |

#### Handler errors — stream state machine

| Code | Meaning | Likely cause / fix |
|---|---|---|
| `handler_no_dbc` | Operation requires a loaded DBC | Call `parseDBC` first |
| `handler_already_streaming` | `aletheia_start_stream` while already streaming | Call `aletheia_end_stream` before restarting |
| `handler_not_streaming` | `aletheia_end_stream` outside a stream | Streaming must be active to end it |
| `handler_stream_not_started` | A data frame with a DBC loaded but no stream started | Call `aletheia_start_stream` before `aletheia_send_frame` |
| `handler_stream_active` | Operation forbidden while streaming | End the stream first (e.g., to reload DBC) |
| `handler_property_parse_failed` | LTL property at the indicated index failed to parse | Check the failing property against the LTL Property Format section |
| `handler_validation_failed` | DBC validation surfaced an error when loading | The envelope's structured `issues` array carries the full list (errors and warnings) — see § Wire shape above |
| `handler_text_roundtrip_failed` | `formatDBCText` refused: the emitted `.dbc` text does not re-parse to the input DBC | The DBC cannot be expressed as round-tripping `.dbc` text (e.g. a multi-value multiplexed signal). The envelope's `issues` array is led by the error-severity `text_roundtrip_divergence` — see [FormatDBCText](#formatdbctext) |
| `handler_non_monotonic_timestamp` | Current frame's timestamp is below the previous frame's | Sort frames by timestamp before streaming — metric LTL operators require monotonicity |

#### Dispatch errors — top-level request routing

| Code | Meaning | Likely cause / fix |
|---|---|---|
| `dispatch_missing_type_field` | Request has no `type` field | Add `"type": "command"` |
| `dispatch_unknown_message_type` | `type` value not recognised | Only `command` is supported |
| `dispatch_invalid_json` | Request was not valid JSON (structured `line`/`column` mark the first unparseable byte) | Validate the JSON before sending |
| `dispatch_request_not_object` | Top-level value is not an object | Wrap in `{...}` |

#### DBC text parse errors — `parseDBCText` / `formatDBCText`

| Code | Meaning | Likely cause / fix |
|---|---|---|
| `dbc_text_parse_failure` | The `.dbc` text could not be parsed (structured `line`/`column` mark the deepest byte any parse attempt reached) | Check the file against the DBC grammar at the reported byte; run `validate` for structural issues |
| `dbc_text_trailing_input` | The top-level parse stopped at the first unparseable statement — structured `line`/`column` mark the exact failing byte inside it, `statement_line`/`statement_column` where the statement starts | Fix the statement at the reported byte |
| `dbc_text_attribute_refinement_failed` | A `BA_DEF_DEF_` / `BA_` / `BA_REL_` entry failed refinement — the message names the offending attribute and whether it is undeclared or its value does not fit the declared type | Declare the attribute via `BA_DEF_` first; keep values inside the declared type (e.g. `ENUM` indices in range) |

Signal-geometry refusals on the text route reuse the JSON route's
`parse_signal_*` codes (both routes run the same entry gate — see the
[ParseDBC](#parsedbc) geometry semantics). They are anchored by the signal's
name (`signal 'NAME': ...`) rather than the positioned `line`/`column`
watermark: the gate runs after the `SG_` line parses, so the offending
statement is already consumed. The positioned channel above remains for
syntactic failures.

---

## Implementation Notes

### FFI Entry Points
- **Commands**: JSON text via `aletheia_process(state, &text)` for every operation but the data frames, the text being its UTF-8 bytes and their count in one `struct aletheia_text`
- **Data frames**: Binary via `aletheia_send_frame(state, &frame)` — streaming hot path
- **Error frames**: Binary via `aletheia_send_error(state, &frame)`, reading its timestamp — bus-error events
- **Remote frames**: Binary via `aletheia_send_remote(state, &frame)`, reading its timestamp and identifier — remote frames
- All four return a JSON response string (freed with `aletheia_free_str`)
- No newline delimiters needed — each FFI call is one complete message
- State is managed via `StablePtr (IORef StreamState)` on the Haskell side

### Sequential Processing
- Calls are processed sequentially within the same process
- No threading or queuing
- Each FFI call blocks until complete and returns immediately
- Data frames return ack or violation immediately

### State Validation
- All state transitions are validated in Agda
- Invalid transitions return error responses
- State machine enforces correct protocol usage

### Type Safety
- JSON parsing happens in Agda (fully verified)
- Malformed JSON is rejected with error message
- All logic uses Agda's type system (`--safe --without-K`)

---

## Structured Logging

*This section is the single source of truth for the structured-log event taxonomy. Other docs that mention the event count or list events should link back here rather than restate.*

All four bindings share the same 16-event vocabulary, so a single downstream log pipeline can consume any of them (Python `logging`, C++ `Logger` callback, Go `slog`, Rust `Logger` trait). Python, C++, and Go emit all 16 events; the Rust binding defines the full vocabulary but does not emit the three `cache.*` events — they instrument an extraction-result memoization cache that binding does not implement (a perf layer, not part of the contract; see `rust/src/log.rs`).

| Category | Level | Events |
|---|---|---|
| Lifecycle | INFO (`rts.cores_mismatch` is WARNING) | `dbc.parsed`, `properties.set`, `stream.started`, `stream.ended`, `rts.cores_mismatch` |
| Frame processing | DEBUG | `frame.processed`, `error_event.sent`, `remote_event.sent` |
| Enrichment diagnostics | WARNING | `enrichment.property_index_oob`, `enrichment.extraction_failed` |
| Extraction cache | DEBUG / WARNING | `cache.hit`, `cache.miss`, `cache.full` |
| Extraction errors | WARNING | `extraction.process_failed`, `extraction.parse_failed` |
| End-of-stream diagnostics | WARNING | `endstream.uncached_atom` |

Each record carries the event name plus structured key/value fields (frame count, property index, reason string, etc.). Per-binding definitions are `python/aletheia/client/_log.py` (`LogEvent` enum), `cpp/src/client.cpp` (inline event literals at the emit sites), `go/aletheia/client.go` + `go/aletheia/ffi.go` (slog emission sites), and `rust/src/log.rs` (`events::*` constants + `events::ALL`). Adding a new event requires adding it to all four bindings and updating this table; note that the Rust parity test (`rust/tests/log_events.rs`) pins `events::ALL` to [`docs/LOG_EVENTS.yaml`](../LOG_EVENTS.yaml) bijectively, so a new YAML row without the matching Rust constant fails CI even if Rust never emits the event.

See [INTERFACES.md § Structured Logging](../reference/INTERFACES.md#structured-logging) for per-binding wiring examples.

---

## See Also

- [DESIGN.md](DESIGN.md) - Overall architecture and design decisions
- [PROJECT_STATUS.md](../../PROJECT_STATUS.md) - Phase completion status and milestones
- [PYTHON_API.md](../reference/PYTHON_API.md) - Python client library
