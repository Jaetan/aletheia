# Aletheia Streaming Protocol

**Purpose**: Complete specification of the FFI protocol for CAN frame analysis with LTL checking. Version and release metadata live in [DISTRIBUTION.md](../development/DISTRIBUTION.md).

---

## Contents

- [Audience](#audience)
- [Overview](#overview)
- [JSON Text](#json-text)
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

The language bindings (Python, C++, Go, Rust) call the Agda/Haskell core through the C ABI of `libaletheia-ffi.so`, declared in `haskell-shim/include/aletheia.h`, which a C caller compiles as C23 and a C++ caller as C++23. The ABI is version 4 (`ALETHEIA_ABI_VERSION`); `aletheia_abi_version()` reports the version a library implements, and a binding refuses a library whose version is not its own.

**Communication Model**:
- `aletheia_process()` takes one JSON command as a `struct aletheia_text`, its UTF-8 bytes and their count: the DBC and property commands (`parseDBC`, `setProperties`, `validateDBC`, `parseDBCText`, `formatDBCText`).
- The [binary entry points](#binary-entry-points) take C values: the stream's lifecycle (`aletheia_start_stream()`, `aletheia_end_stream()`), its events (`aletheia_send_frame()`, `aletheia_send_error()`, `aletheia_send_remote()`), extraction (`aletheia_extract_signals()`), the DBC's export (`aletheia_format_dbc()`), the binary-output build, update and extraction (`aletheia_build_frame_bin()`, `aletheia_update_frame_bin()`, `aletheia_extract_signals_bin()`), and the text entries (`aletheia_parse_decimal()`, `aletheia_parse_time_bound()`, `aletheia_check_property()`, `aletheia_format_rational()`).
- A session is the handle `aletheia_init()` returns, freed with `aletheia_close()`; `aletheia_free_str()` and `aletheia_free_buf()` free what the entries return, and `aletheia_allocated_bytes()` reports the bytes the runtime has allocated.
- One call per response (request-response).
- A session handle is used from one thread at a time; different handles may be used from different threads.
- Everything runs in-process in `libaletheia-ffi.so`, with no subprocess or IPC.

**State Machine**:
~~~
WaitingForDBC → ParseDBC → ReadyToStream → SetProperties → ReadyToStream
                                          → StartStream → Streaming → SendFrame* → Streaming
                                                                     → EndStream → ReadyToStream
~~~

A `parseDBC` or `parseDBCText` that loads its DBC enters `ReadyToStream` from any state, with no property and an empty signal cache, ending a stream in progress; `setProperties` during a stream is refused with `handler_stream_active`.

---

## JSON Text

A command is RFC 8259 JSON text, and so is every reply. The kernel's parser is that grammar, proven both ways: every text it accepts whole is in RFC 8259's grammar, written as an Agda type in `Aletheia.Protocol.JSON.RFC8259` (`parseJSON-sound`), and it reads back every value the kernel writes whose numbers have a numerator magnitude and a denominator below 2^128 (`parseJSON-formatJSONChars`), as every reply's numbers have (`formatResponse-readable`).

- A command is one value, with whitespace around it and nothing after it. Whitespace is space, horizontal tab, line feed and carriage return.
- An integer part is `0` or starts with a digit from 1 to 9.
- A string holds no raw character below U+0020. A `\uXXXX` escape names a Unicode scalar value: a surrogate pair (`\ud83d\ude00`) is read as the one character it encodes, and a lone surrogate half is refused.
- Text outside the grammar is refused with `dispatch_invalid_json`, its `line` and `column` those of the first character the parser cannot read.

A reply escapes `"`, `\` and every character below U+0020, in keys as in values: `\b`, `\f`, `\n`, `\r` and `\t` in their short form, the rest as `\u00XX`. Every reply is in the grammar (`reply-is-JSONText`) and nests at most 8 deep (`formatResponse-depth`).

---

## Message Types

A request is a JSON object whose `"type"` field decides how it is processed: a JSON value that is not an object is refused with `dispatch_request_not_object`, an object without `"type"` with `dispatch_missing_type_field`, and a `"type"` other than `"command"` with `dispatch_unknown_message_type`.

### Type Tags
- `"command"`: the DBC and property commands, `parseDBC`, `setProperties`, `validateDBC`, `parseDBCText` and `formatDBCText`, named by the `"command"` field. The stream and its frames have **no JSON command form**; they are the [binary entry points](#binary-entry-points), and a command naming one, such as `startStream`, is refused with `route_unknown_command`.

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
  "warnings": [{"severity": "warning", "code": "offset_scale_range", "detail": "Message 'SpeedMessage', signal 'Speed': its bits carry values above the declared maximum"}]
}
~~~

The success response echoes the canonical parsed body (`dbc`) and `warnings`, the warning-severity validation issues, in the same `{severity, code, detail}` element shape as [ValidateDBC](#validatedbc)'s `issues`. Warnings never block a load; error-severity issues refuse it with `handler_validation_failed` (see [§ Wire shape](#wire-shape)).

**Response** (Error):
~~~json
{
  "status": "error",
  "code": "parse_missing_field",
  "message": "ParseDBC: missing 'messages' field"
}
~~~

**Fields**:
- `dbc.version`: the DBC's version string
- `dbc.messages`: Array of CAN message definitions
  - `id`: CAN message ID (0-2047 for standard, 0-536870911 for extended)
  - `name`: Message name (string)
  - `dlc`: the payload's byte count: 0 to 8, or a CAN-FD size 12, 16, 20, 24, 32, 48 or 64 (`parse_invalid_dlc_bytes` otherwise)
  - `extended`: Boolean, true for 29-bit IDs
  - `sender`: Node that sends this message
  - `signals`: Array of signal definitions
    - `name`: Signal name (must be unique within message)
    - `startBit`: Bit position in frame (below the frame's bit count, `dlc * 8`)
    - `length`: Signal length in bits (at least 1, at most `dlc * 8`)
    - `byteOrder`: "little_endian" or "big_endian"
    - `signed`: Boolean, true for signed integers
    - `factor`: Scaling factor, a number (see [Rational Number Encoding](#rational-number-encoding))
    - `offset`: Offset applied after scaling
    - `minimum`: Minimum physical value
    - `maximum`: Maximum physical value
    - `presence`: "always" for always-present signals (default if omitted); multiplexed signals use `multiplexor` and `multiplex_values` fields instead (see Multiplexing Support below)

**Signal geometry: frame-capacity bound, refuse posture**. A signal's bit geometry is bounded by its message's frame, `dlc * 8` bits; the byte count already tells classic CAN from CAN-FD, so there is no separate per-protocol bound. The kernel checks the submitted values at entry and refuses out-of-frame geometry with a typed error naming them (`parse_signal_start_bit_exceeds_frame`, `parse_signal_bit_length_exceeds_frame`, `parse_signal_bit_length_zero`; values are never normalized or clamped into range). For big-endian (Motorola) signals, `startBit` names the physical MSB and the descending run of `length` bits must stay inside the frame (`parse_signal_big_endian_overflow` otherwise); the textbook full-frame layout, MSB at bit 7 descending through the whole frame, is accepted. Both DBC entry routes (this command and [ParseDBCText](#parsedbctext)) run the same gate and emit the same codes; text-route refusals are anchored by the signal's name (`signal 'NAME': ...`) rather than a byte position, because the gate runs after the `SG_` line parses.

**State Transition**: any state → `ReadyToStream`, with no property

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

Signal is only present when the multiplexor signal's value is in the `multiplex_values` array, each value at most 2^128 − 1 (`max-multiplex-value`). Single-value mux uses a one-element array (e.g., `[1]`); extended mux (SG_MUL_VAL_) uses multiple values (e.g., `[0, 1, 3]`). A request omits `presence` for a multiplexed signal or gives it as `"multiplexed"`, and a reply writes `"presence": "multiplexed"`.

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
      "unit": "degC",
      "multiplexor": "MuxSignal",
      "multiplex_values": [1]
    }
  ]
}
~~~

**Behavior**:
- When `MuxSignal == 0`, only `Signal_Mux0` is extracted besides `MuxSignal`
- When `MuxSignal == 1`, only `Signal_Mux1` is extracted besides `MuxSignal`
- A signal its multiplexor's value does not select is listed in the extraction's `absent`, not in `values` or `errors`
- The multiplexor must be a signal of the same message (`multiplexor_not_found` otherwise); one that is not always present loads with the warning `mux_master_incoherent`

**Implementation**: See [DESIGN.md](DESIGN.md) for the Agda module structure. The multiplexor logic is in the CAN signal extraction module; signal presence types are in the DBC types module.

---

### ParseDBCText

Load a DBC from `.dbc` file text, read by the verified Agda text parser, the text-level counterpart of [ParseDBC](#parsedbc).

**Request** (the DBC of [ParseDBC](#parsedbc) as `.dbc` text, its transmitter `ECU` declared in `BU_`):
~~~json
{"type": "command", "command": "parseDBCText", "text": "VERSION \"1.0\"\n\nNS_ :\n\nBS_:\n\nBU_: ECU\n\nBO_ 256 SpeedMessage: 8 ECU\n SG_ Speed : 0|16@1+ (0.1,0) [0|300] \"km/h\" Vector__XXX\n"}
~~~

**Response** (Success, its `dbc` echo elided):
~~~json
{"status": "success", "dbc": {...}, "warnings": [{"severity": "warning", "code": "offset_scale_range", "detail": "Message 'SpeedMessage', signal 'Speed': its bits carry values above the declared maximum"}]}
~~~

**Response** (Error, the same text without the colon after `SpeedMessage`):
~~~json
{"status": "error", "code": "text_trailing_input", "message": "ParseDBCText: parse failed at line 9, column 22 (first unparseable statement starts at line 9, column 1)", "line": 9, "column": 22, "statement_line": 9, "statement_column": 1}
~~~

**Fields**:
- `text`: the `.dbc` file image, a string; absent, `route_missing_field`.

The text is scanned before it is parsed, a character outside the DBC text set refused with `dbc_invalid_character` at its `line` and `column`; a text the grammar refuses answers `text_parse_failure` or `text_trailing_input` with the positions [§ Wire shape](#wire-shape) describes. A parsed text then goes through the bounds and the validation `parseDBC` applies, with the same codes, and loads the same way, its success reply in the shape of [ParseDBC](#parsedbc)'s.

**State Transition**: any state → `ReadyToStream`, with no property

---

### ValidateDBC

Validate a DBC definition for structural correctness, returning every issue found.

**Request**:
~~~json
{
  "type": "command",
  "command": "validateDBC",
  "dbc": { ... }
}
~~~

**Response** (to a DBC whose message `SpeedMessage` carries two overlapping signals and whose message `EmptyMessage` carries none):
~~~json
{"status": "validation", "has_errors": true, "issues": [{"severity": "error", "code": "signal_overlap", "detail": "Message 'SpeedMessage', signals 'Speed' and 'Brake' overlap"}, {"severity": "warning", "code": "empty_message", "detail": "Message 'EmptyMessage': message has no signals"}]}
~~~

**Fields**:
- `dbc`: Complete DBC definition (same schema as `parseDBC`)
- Response `has_errors`: true if any issue has severity "error"
- Response `issues`: Array of validation issues

A DBC the JSON parse or a size bound refuses is answered with that error instead, e.g. `{"status": "error", "code": "parse_invalid_dlc_bytes", "message": "ValidateDBC: message 'M': DLC 15 is not a valid CAN byte count"}`.

**Issue Codes**:
- **Error**: `duplicate_message_id`, `duplicate_signal_name`, `factor_zero`, `multiplexor_not_found`, `multiplexor_cycle`, `min_exceeds_max` (on a signal, a numeric attribute definition or an environment variable), `signal_exceeds_dlc`, `signal_overlap`, `bit_length_zero`, `range_exceeds_bits`, `value_description_key_out_of_range`
- **Warning**: `global_name_collision`, `duplicate_message_name`, `offset_scale_range`, `empty_message`, `start_bit_out_of_range`, `bit_length_excessive`, `multiplexor_non_unit_scaling`, `duplicate_attribute_name`, `unknown_comment_target`, `unknown_message_sender`, `unknown_signal_receiver`, `unknown_value_description_target`, `multi_value_mux_selector`, `mux_master_incoherent`

`multi_value_mux_selector` and `mux_master_incoherent` mirror the [FormatDBCText](#formatdbctext) round-trip checker's diagnostics: such a DBC loads and streams, but `formatDBCText` refuses it.

**State Requirements**: Does NOT require `parseDBC`. Does NOT modify client state (read-only probe).

---

### FormatDBCText

Render a DBC definition (JSON wire shape) back to `.dbc` file text via the verified Agda formatter, the text-level inverse of `parseDBCText`.

**Always strict.** `formatDBCText` returns text **only** when that text provably re-parses to the exact input DBC: `parseDBCText(formatDBCText(d).text)` reproduces `d`, an empty `nodes` list filled with every message transmitter. There is no lenient/best-effort mode and no `strict` flag: a flag would imply you might sometimes want text that does *not* round-trip, which contradicts the command's whole purpose (never emit silently-lossy output). A DBC that cannot be expressed as round-tripping `.dbc` text, for example a signal multiplexed on **multiple** selector values, which the JSON model admits but the `.dbc` grammar cannot encode, is **refused** with a typed error rather than emitting text that would quietly lose information. The emitted-text round-trip guarantee is machine-checked (`formatDBCTextResult-sound` in `Aletheia.Protocol.Handlers.Properties.FormatDBCText`), not merely asserted.

A DBC past a size bound is refused with `input_bound_exceeded` before anything is formatted, exactly as the load routes refuse it (see [Limits](#limits)), so the command never emits text a load refuses for its size. The `nodes` list it fills before formatting is held to the node bound too.

**Request**:
~~~json
{
  "type": "command",
  "command": "formatDBCText",
  "dbc": { ... }
}
~~~

**Response** (Success, the DBC of [ParseDBC](#parsedbc) round-tripping):
~~~json
{
  "status": "success",
  "text": "VERSION \"1.0\"\n\nNS_ :\n\tNS_DESC_\n\tCM_\n\tBA_DEF_\n\tBA_\n\tVAL_\n\tCAT_DEF_\n\tCAT_\n\tFILTER\n\tBA_DEF_DEF_\n\tEV_DATA_\n\tENVVAR_DATA_\n\tSGTYPE_\n\tSGTYPE_VAL_\n\tBA_DEF_SGTYPE_\n\tBA_SGTYPE_\n\tSIG_TYPE_REF_\n\tVAL_TABLE_\n\tSIG_GROUP_\n\tSIG_VALTYPE_\n\tSIGTYPE_VALTYPE_\n\tBO_TX_BU_\n\tBA_DEF_REL_\n\tBA_REL_\n\tBA_SGTYPE_REL_\n\tSG_MUL_VAL_\n\nBS_:\n\nBU_: ECU\n\nBO_ 256 SpeedMessage: 8 ECU\n SG_ Speed : 0|16@1+ (0.1,0.0) [0.0|300.0] \"km/h\" Vector__XXX\n\n",
  "issues": []
}
~~~

**Response** (Refusal, the [Multiplexing Support](#multiplexing-support) message with `Signal_Mux0` on `[0, 2]`):
~~~json
{
  "status": "error",
  "code": "handler_text_roundtrip_failed",
  "message": "FormatDBCText: text round-trip failed: re-parsing the emitted text does not reproduce the input DBC",
  "has_errors": true,
  "issues": [
    {"severity": "error", "code": "text_roundtrip_divergence", "detail": "re-parsing the emitted text does not reproduce the input DBC"},
    {"severity": "warning", "code": "multi_value_mux_selector", "detail": "signal 'Signal_Mux0': multi-value mux selector — text form emits only the first selector value"}
  ]
}
~~~

**Fields**:
- `dbc`: Complete DBC definition (same schema as `parseDBC` input); absent → `route_missing_dbc_field`.
- Success `text`: the `.dbc` file image (a string).
- Success `issues`: **warning-severity** round-trip diagnostics (`wfTextIssues`). This list MAY be non-empty even on a successful round-trip: a warning flags a construct *outside the proven well-formed-text envelope* that nonetheless round-tripped; it is advisory, never a failure.
- Refusal `issues`: led by the error-severity `text_roundtrip_divergence` (the handler prepends it on every refusal), followed by the same warning diagnostics. `has_errors` is `true`.

The refusal envelope shares the `{severity, code, detail}` element shape, the `has_errors` flag, and the one-issue-decoder contract with the `handler_validation_failed` envelope (see [§ Wire shape](#wire-shape)), so a binding decodes both with the same issue decoder.

**Round-trip issue codes** (the codes this command's checker introduces; all severity **warning** except `text_roundtrip_divergence`). They are documented separately from the structural-validation codes under [ValidateDBC](#validatedbc), with two shared codes: `multi_value_mux_selector` and `mux_master_incoherent` are also emitted by `validateDBC` and the DBC-loading routes as warning-class mirrors driven by the same kernel deciders (a shape that loads cleanly but cannot round-trip to `.dbc` text is named without calling `formatDBCText`); the remaining codes are emitted by `formatDBCText` only:

| Code | Severity | Meaning |
|---|---|---|
| `text_roundtrip_divergence` | error | The emitted `.dbc` text does not re-parse to the input DBC: the refusal marker, prepended on every refusal |
| `multi_value_mux_selector` | warning | A signal is multiplexed on more than one selector value, expressible in JSON, not in the `.dbc` `SG_` grammar |
| `mux_master_incoherent` | warning | A multiplexed message's multiplexor master signal is missing or inconsistent |
| `unknown_attribute_name` | warning | A `BA_` attribute value references a name never declared via `BA_DEF_` |
| `attribute_value_type_mismatch` | warning | An attribute value does not fit its declared `BA_DEF_` type |
| `attribute_enum_empty` | warning | An `ENUM` attribute type declares no labels |
| `attribute_enum_default_unstable` | warning | An `ENUM` attribute's `BA_DEF_DEF_` default does not resolve to a stable label |

**State Requirements**: Does NOT require `parseDBC`. Does NOT modify client state (read-only): pass any DBC value (typically from `parseDBCText`, `formatDBC`, or the JSON converters).

Every binding surfaces this as `format_dbc_text(dbc)`: `text` + `issues` on success, and a typed round-trip-refusal error (Python `TextRoundTripFailedError`, Go `*TextRoundTripFailedError`, C++ `AletheiaError` with `ErrorKind::TextRoundtrip`, Rust `Error::TextRoundtripFailed`) carrying the diverging issue list (see the `dbc_text_roundtrip_check` row in [FEATURE_MATRIX.yaml](../FEATURE_MATRIX.yaml)).

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

**Response** (Error, no DBC loaded):
~~~json
{
  "status": "error",
  "code": "handler_no_dbc",
  "message": "SetProperties: DBC not loaded"
}
~~~

**State Requirements**: Must be in `ReadyToStream` state (after `parseDBC` or `parseDBCText`); during a stream it is refused with `handler_stream_active`

**State Transition**: `ReadyToStream` → `ReadyToStream` (idempotent)

A `signal` is decided as it is read, by the identifier decision a parsed DBC's names go through and then the loaded DBC. Each refusal of the identifier decision is the one it gives a parsed DBC's name, its `field` being `signal`: a name past 128 characters is `input_bound_exceeded` with `identifier_length`, one holding a character outside ASCII `dbc_invalid_character` with its `index` and `code_point`, a DBC keyword `dbc_keyword_name`, and one that is not an identifier `parse_invalid_identifier`; a name no signal of the loaded DBC carries is then refused with `handler_unknown_signal`, which names no `field`. The first refusal ends the command, which keeps none of its properties and leaves the ones set before in place.

See [LTL Property Format](#ltl-property-format) section below for complete schema.

---

## Binary Entry Points

The stream and its frames go through C entry points that take their input as C values, a structure passed by pointer, never as JSON; `aletheia.h` fixes the size, alignment and field offsets of every structure for LP64 targets, each asserted there. A JSON-answering entry returns a string the caller frees with `aletheia_free_str()`; a binary-output entry fills a `struct aletheia_buffer`, and each of the three parse and check entries its own result structure. Every binding drives the stream through these entries.

**The kernel parses every frame.** `Aletheia.CAN.Frame.Parse` reads a frame's fields as the caller passed them and refuses one that breaks a rule before any state changes, checking them in this order and the payload byte by byte, so the first rule broken is the one reported:

| Rule | Code |
|---|---|
| The timestamp a stream entry reads (`aletheia_send_frame`, `aletheia_send_error`, `aletheia_send_remote`) is at most 2⁶⁴ − 1 | `parse_timestamp_past_wire` |
| A standard identifier is below 2048, an extended one below 2²⁹ | `parse_std_can_id_out_of_range` / `parse_ext_can_id_out_of_range` |
| The DLC is at most 15 | `parse_dlc_code_out_of_range` |
| `data_len` is the DLC's byte count: the code itself up to 8, then 12, 16, 20, 24, 32, 48, 64 | `parse_payload_length_mismatch` |
| Every payload byte is below 256 | `parse_payload_byte_out_of_range` |

`timestamp` is a `uint64_t` and `data_len` a `uint8_t`, so neither a timestamp past 2⁶⁴ − 1 nor a payload over 255 bytes reaches the kernel. Every binding checks a payload against its DLC before calling, so these codes reach only a caller of the C entries themselves.

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

`aletheia_end_stream()` closes the stream, returning the session to `ReadyToStream` (it can stream again), and answers each property's final verdict in a [Complete Response](#complete-response) (see [Streaming Semantics](#streaming-semantics-soundness-vs-completeness)), here for `always` `Speed < 250` after one frame carrying `Speed` 100:

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

**Why binary?** It removes JSON serialization and parsing from the streaming hot path (see [BENCHMARKS.md](../development/BENCHMARKS.md#canonical-results) for each binding's throughput on it).

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
| Parse the frame (rules above) | ✅ timestamp, identifier, DLC, payload | ✅ timestamp | ✅ timestamp, identifier |
| Extract signals from payload | ✅ | no | no |
| Update signal cache | ✅ | no | no |
| Advance LTL clock by `ts` | ✅ | ✅ | ✅ |
| Re-evaluate active properties | ✅ | ✅ (no signal change, but metric windows may expire) | ✅ (no signal change, but metric windows may expire) |
| Emit verdict if a property terminates | ✅ | ✅ | ✅ |

The key consequence of re-evaluating at every event: **error and remote frames can finalize a metric `eventually` window**, even though they carry no signal updates. This matches LTLf semantics: the clock advances, so any property whose window closes between events resolves on the next timestamp regardless of the event kind.

Outside a stream, with or without a DBC, an error or remote frame that breaks no rule above is answered `ack` and leaves the session as it was, its clock included; a data frame is refused there, as above.

#### Response shape

The response shape is identical to `aletheia_send_frame`'s: an `ack` if no property terminated, a property batch if one did, or a refusal, `handler_non_monotonic_timestamp` for a backward timestamp and the `parse_*` code of a frame breaking a rule above (`{"status": "error", "code": "parse_std_can_id_out_of_range", "message": "standard CAN ID 4000 exceeds limit 2047"}` for a remote frame's standard identifier of 4000). The binding wrappers `send_error()` / `send_remote()` (Python, C++, Go, Rust) parse the same response types they use for data frames.

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
{"status": "success", "dbc": {"version": "1.0", "messages": [...], "signalGroups": [], "environmentVars": [], "valueTables": [], "nodes": [], "comments": [], "attributes": [], "unresolvedValueDescs": []}}
~~~

Without a DBC it answers `handler_no_dbc`. The distinct [`formatDBCText`](#formatdbctext) command renders a DBC as `.dbc` text.

### aletheia_build_frame_bin, aletheia_update_frame_bin and aletheia_extract_signals_bin

The binary-output entries answer 0 on success and 1 on failure, with their result in a `struct aletheia_buffer` (see `aletheia.h`): a build or an update writes the frame's bytes into the caller's buffer, which must hold the DLC's byte count, and sets `size` to the count written; an extraction allocates the packed layout below, freed with `aletheia_free_buf()`.

Signal values for a build or an update cross as one `struct aletheia_signal_values`: `count` signal indices (`uint32_t`) and as many values, each a `struct aletheia_rational`, whose `numerator` and `denominator` are magnitudes held as `struct aletheia_uint128` (two `uint64_t` words, `lo` then `hi`) and whose sign is the byte `negative`. The kernel builds each value as an exact rational in lowest terms and refuses a zero denominator with `parse_non_positive_denominator` (and arrays of unequal length with `parse_signal_array_length_mismatch`, which the C structure, carrying one count, cannot express).

A build or an update checks the request before writing anything: every requested signal must fit the frame (`frame_signal_past_frame_end`) and no two may share a bit (`frame_signals_overlap`). Each value is then checked in turn, and a refusal leaves the caller's buffer untouched: a value outside the signal's declared range is refused with `frame_value_out_of_range`, and one that no integer raw value scales to exactly with `frame_value_not_representable`. An accepted value is written exactly, and the frame reads it back unchanged wherever it carries the signal: always, or for a multiplexed signal when its multiplexor's value selects it.

On failure the buffer's `err` is the JSON error envelope every other entry answers with, freed with `aletheia_free_str()`:

~~~json
{"status": "error", "code": "parse_non_positive_denominator", "message": "non-positive denominator 0"}
~~~

The code is the kernel's refusal, or `ffi_validation_error` for a NULL pointer the entry needs (the state, the frame, the signal values, or an array or data with a non-zero count) or a buffer smaller than the frame the kernel built, such as `{"status":"error","code":"ffi_validation_error","message":"aletheia_build_frame_bin: out size 4 < 8 frame bytes"}`. A NULL buffer, which has no `err` to set, answers 1 with nothing written.

An extraction's buffer holds these parts back to back, every integer in the host's byte order (little-endian on x86_64 and ARM64), one value of 35 bytes making a 49-byte buffer:

| Part | Size in bytes | Contents |
|---|---|---|
| Header | 10 | `nValues` u16, `nErrors` u16, `nAbsent` u16, `reasonBytes` u32 |
| Values | 35 each | signal index u16, `negative` u8, numerator magnitude u128, denominator u128, each u128 its low then its high u64 |
| Errors | 3 each | signal index u16, error code u8 (`extractionErrorCodeToℕ` in `Aletheia.CAN.BatchExtraction`) |
| Offsets | 4 × (nErrors + 1) | u32 cumulative offsets into Reasons: the first 0, non-decreasing, the last `reasonBytes` |
| Reasons | `reasonBytes` | UTF-8; error *i*'s reason is the bytes from offset *i* to offset *i* + 1, the text the JSON entry gives |
| Absent | 2 each | signal index u16 |

### aletheia_parse_decimal, aletheia_parse_time_bound, aletheia_check_property and aletheia_format_rational

~~~c
int8_t aletheia_parse_decimal(const struct aletheia_text *input, struct aletheia_decimal *out);
int8_t aletheia_parse_time_bound(const struct aletheia_text *input, struct aletheia_time_bound *out);
int8_t aletheia_check_property(const struct aletheia_text *property, struct aletheia_property_check *out);
char *aletheia_format_rational(const struct aletheia_rational *value);
~~~

These entries decide a text as the kernel does, so no binding decides it. The first three answer 0 on success and 1 on refusal and write every field of `out` on every call: `err` is NULL on success and otherwise the JSON error envelope, freed with `aletheia_free_str()`. A text `struct aletheia_text` refuses is `ffi_validation_error`, and a NULL `out` answers 1 with nothing written.

- `aletheia_parse_decimal`: the exact rational a decimal text denotes, in lowest terms, its numerator magnitude and denominator each at most 2^128 − 1, into `value` (`0.25` gives numerator 1 and denominator 4, `-1.5` numerator 3, denominator 2 and `negative` 1). A text outside the decimal grammar is refused, `abc` with `{"status": "error", "code": "text_parse_failure", "message": "parse failed at line 1, column 1", "line": 1, "column": 1}`.
- `aletheia_parse_time_bound`: a decimal text of microseconds, decided as a metric operator's `timebound` is, into `microseconds`, at most 18446744073709551615. A negative or fractional number is refused with the reason alone, `-1` with `{"status": "error", "code": "handler_property_refused", "message": "timebound -1 is negative"}`, and a larger one with `input_bound_exceeded` naming the field `time bound`.
- `aletheia_check_property`: one property's JSON, read as `setProperties` reads a property, before any session holds it. A text that is not JSON is refused with `dispatch_invalid_json` and a property with `handler_property_refused` and the reason, `{"operator": "always"}` with `{"status": "error", "code": "handler_property_refused", "message": "field 'formula' is missing"}`; a signal name is decided as an identifier, and whether a DBC carries it is left to `setProperties`.
- `aletheia_format_rational`: the string every binding prints for a rational, `0.25` for 1/4, `-1/3` for −1/3 and `100` for 100/1; a NULL rational answers NULL.

---

## Response Types

### Success Response
~~~json
{"status": "success", "message": "Properties set successfully"}
~~~
The reply to `setProperties`, and to `aletheia_start_stream` with the message `Streaming started successfully`. The DBC commands and extraction answer `"status": "success"` with their own fields in place of `message`.

### Error Response
~~~json
{"status": "error", "code": "handler_stream_active", "message": "SetProperties: stream still active"}
~~~
Every error carries `code` and `message`, and the fields its code adds (see [Error Code Reference](#error-code-reference)).

### Acknowledgment Response
~~~json
{"status": "ack"}
~~~
The reply to a data, error or remote frame at which no property reaches a verdict, and to an error or remote frame outside a stream.

### Property Batch Response
The reply to a frame at timestamp 100 carrying `Speed` 260.0, the properties being eventually `Speed > 50` and always `Speed < 250`:
~~~json
{"type": "property_batch", "results": [{"type": "property", "status": "holds", "property_index": 0}, {"type": "property", "status": "fails", "property_index": 1, "timestamp": 100, "reason": "Atomic: predicate failed"}]}
~~~

A data, error or remote frame at which properties reach a verdict answers one batch, its `results` ordered as [aletheia_send_frame](#aletheia_send_frame) says, each property that holds dropped from the active set. The kernel proves `results` non-empty (`NonEmptyList` in `Aletheia.Protocol.Message`, `replyNonEmpty` in `Aletheia.Protocol.ReplyRange`).

**Inner entry fields** (each `results[i]`):
- `type`: always `"property"`
- `status`: `"holds"` or `"fails"`; `"unresolved"` appears only in a [Complete Response](#complete-response)
- `property_index`: the property's zero-based position in the `setProperties` list, a natural number at most 2⁶⁴ − 1
- `timestamp`: with `fails` only, a natural number at most 2⁶⁴ − 1; in a batch, the timestamp in microseconds of the event that decided the violation
- `reason`: with `fails` and `unresolved`, the kernel's explanation

### Complete Response
The reply to `aletheia_end_stream` after one frame carrying `Speed` 10.0, the properties being always `Speed < 250` and eventually `Temp > 0`, no frame carrying `Temp`:
~~~json
{"status": "complete", "results": [{"type": "property", "status": "holds", "property_index": 0}, {"type": "property", "status": "unresolved", "property_index": 1, "reason": "Atomic: predicate never resolved at end of stream"}], "warnings": [{"kind": "uncached_atom", "property_index": 1, "detail": "Temp"}]}
~~~
`results` carries, in the inner entry shape of [Property Batch Response](#property-batch-response), the final verdict of each property but those a batch answered `holds`, which have left the stream; `warnings` carries the end-of-stream diagnostics (see [§ End-of-stream Warnings](#end-of-stream-warnings)).

#### End-of-stream Warnings

`warnings` on the `complete` reply is a list, possibly empty, of the kernel's end-of-stream diagnostics; each names a property of `results` and leaves its verdict as it is.

**Wire shape** (every binding decodes the same JSON):

| Field | Type | Description |
|---|---|---|
| `kind` | string | `"uncached_atom"`, the one kind the kernel writes, proven by `replyText` in `src/Aletheia/Protocol/ReplyRange.agda`. Each binding refuses a `kind` that is not a string and reads any string: Python and Go keep the word as written, C++ and Rust read it as their one `WarningKind`, `UncachedAtom`. |
| `property_index` | integer | The property's zero-based position in the `setProperties` list. |
| `detail` | string | The signal no frame of the stream carried. |

**Defined warning kinds**:

- **`uncached_atom`**: one warning per atom whose signal no frame of the stream carried, so a property with two such atoms has two; `detail` names the signal. See [`Aletheia.Protocol.Adequacy.StreamingWarm`](../../src/Aletheia/Protocol/Adequacy/StreamingWarm.agda) for the adequacy theorem: a stream that carries every atom's signal leaves every atom cached.

**Evolution rule (binding contract)**:

Adding a new `kind` requires a coordinated change:

1. Extend the kernel's `WarningKind`, its word in `Aletheia.Protocol.ResponseFormat`, and the `warnings` rows of `replyText` and `replyRange` in `Aletheia.Protocol.ReplyRange`.
2. Add a new `endstream.<kind>` row to [`docs/LOG_EVENTS.yaml`](../LOG_EVENTS.yaml).
3. Give each of the four bindings' warning kinds the new member, read from its word, and a matching log event emit site in its `end_stream` / `EndStream` (level: `warn`).
4. Add a per-binding parity test that exercises the new kind.
5. Add a `#### `endstream.<kind>`` heading to [`docs/operations/RUNBOOK.md`](../operations/RUNBOOK.md).
6. Update this section's table of defined kinds.
7. Add a CHANGELOG entry under `Added` per Public API stability discipline.

Removing or renaming a `kind` is a breaking wire change (downstream collectors may be filtering on the literal name) and is governed by the CHANGELOG `Removed` discipline.

**Logging mirror**: each binding's `end_stream` logs every warning as `endstream.uncached_atom` (level `warn`) with `property_index` and `detail`, so operators can grep for a property; Python, Go and C++ also count them as `numWarnings` on `stream.ended`, whose Rust form carries `results` alone. See [`docs/LOG_EVENTS.yaml`](../LOG_EVENTS.yaml) and the per-binding parity tests.

---

## LTL Property Format

### Signal Predicates (Atomic)

Every `value`, `min`, `max`, `delta` and `tolerance` is a number in either form of [Rational Number Encoding](#rational-number-encoding).

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
Holds when `min <= value <= max`; a `min` above `max` is refused (`between: min 90 exceeds max 60`).

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
Directional change detection. A delta of 0 or more: `curr - prev >= delta` (increased by at least delta). A negative delta: `curr - prev <= delta` (decreased by at least |delta|).

#### StableWithin
~~~json
{
  "predicate": "stableWithin",
  "signal": "Temperature",
  "tolerance": 2.0
}
~~~
Magnitude tolerance: `|curr - prev| <= tolerance`. Tests that a signal's value stayed within tolerance of its previous value; a negative tolerance is refused.

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
Property must hold at the next frame: `next` at a frame holds when its `formula` holds from the frame that follows. At the last frame of a stream there is no following frame, and `next` fails whatever its `formula`: the strong next of Roşu, "Finite-Trace Linear Temporal Logic: Coinductive Completeness" (RV 2016), the finite-trace semantics the kernel's LTL follows.

#### Weak Next
~~~json
{
  "operator": "weakNext",
  "formula": {...}
}
~~~
Property must hold at the next frame when there is one: `weakNext` at a frame holds when its `formula` holds from the frame that follows, and at the last frame of a stream it holds whatever its `formula`, as Roşu's weak next does. Use it for "if X then next Y" where X may hold on the final frame, at which `next` fails.

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

#### Never
~~~json
{
  "operator": "never",
  "formula": {...}
}
~~~
`formula` must hold at no frame: `always` of `not formula`.

#### Implies
~~~json
{
  "operator": "implies",
  "antecedent": {...},
  "consequent": {...}
}
~~~
`consequent` must hold where `antecedent` does: `or` of `not antecedent` and `consequent`.

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

A metric operator's `timebound` is a JSON number of whole microseconds from 0 to 18446744073709551615 (2^64 − 1, `max-time-bound`), the range of a frame's timestamp. A negative one is refused with `handler_property_parse_failed` (`timebound -1 is negative`), a fractional one likewise (`timebound 1.5 is not a whole number`), a larger one with `input_bound_exceeded` naming the field `time bound`, and a `{numerator, denominator}` object as not a number.

---

### Streaming Semantics: Soundness vs. Completeness

Aletheia's incremental evaluator is **sound** but not **complete**: a verdict is `holds`, `fails` or `unresolved`. The distinction matters when interpreting a `"complete"` response:

- **Sound**: every definite verdict, `holds` or `fails`, is correct relative to the observed trace. `LTL/Adequacy.agda` proves the monitor's verdicts sound against the denotational semantics of `LTL/Semantics.agda`, lifted to the production simplify/stepL loop by `LTL/Adequacy/Pipeline.agda` (`pipeline-adequate`), and discharged for the signal-cache premise by `Protocol/Adequacy/StreamingWarm.agda` (`streaming-warms-cache`) **provided** the trace satisfies `AllObserved dbc σ atoms`, i.e., every predicate's target signal is extracted from at least one frame in the trace. The runtime does not refuse a trace that breaks `AllObserved`; it names each predicate whose signal no frame carried with an `uncached_atom` warning at the end of the stream.
- **Not complete**: a property can end `unresolved` when an atomic predicate it waits on is still undecided at the end of the stream, its signal never extracted from any frame.

**At the end of the stream** a property still pending is decided on the trace that ended (`finalizeL` in `Aletheia.LTL.Coalgebra`): an atomic predicate still waiting is `unresolved`; `always`, `release`, `metricAlways` and `metricRelease` answer `holds`; `eventually`, `until`, `metricEventually` and `metricUntil` answer `fails` with an end-of-stream reason, whether or not a metric window has elapsed; a `next` whose following frame never came fails and a `weakNext` holds, as [Next](#next) and [Weak Next](#weak-next) say; `not`, `and` and `or` combine their operands' verdicts in three-valued logic.

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

Every number is an exact rational, its numerator's magnitude and its denominator each at most 2^128 − 1 (`max-rational-component-magnitude`, see [Limits](#limits)), written in one of two formats:

### 1. Decimal Format (Input)
~~~json
{"value": 0.25}
~~~
A JSON number, accepted in input and read as the exact rational it denotes.

### 2. Object Format (Output)
~~~json
{"numerator": 1, "denominator": 4}
~~~
A reply writes a value that is not an integer this way, in lowest terms with the sign on the numerator, and an integer as itself.

**Why Two Formats?**
- Decimal format is convenient for users (e.g., `"factor": 0.1`)
- Object format preserves exact values (e.g., 1/3 has no finite decimal)
- The parser accepts both: a property's numbers take any rational, and a DBC's numbers a rational whose decimal expansion terminates, another refused with `parse_non_terminating_rational`

**Examples** (a DBC's `factor`, `offset` and `maximum` as a reply writes them):
- `0.25` → `{"numerator": 1, "denominator": 4}`
- `-1.5` → `{"numerator": -3, "denominator": 2}`
- `100` → `100`

---

## Example Session

The DBC is the one of [ParseDBC](#parsedbc), its `dbc` echo elided, and the two properties are `always` `Speed` below 300 and `eventually` `Speed` above 250, each in the form of [SetProperties](#setproperties).

### 1. Parse DBC
~~~json
>>> {"type": "command", "command": "parseDBC", "dbc": {...}}
<<< {"status": "success", "dbc": {...}, "warnings": [{"severity": "warning", "code": "offset_scale_range", "detail": "Message 'SpeedMessage', signal 'Speed': its bits carry values above the declared maximum"}]}
~~~

### 2. Set Properties
~~~json
>>> {"type": "command", "command": "setProperties", "properties": [{...}, {...}]}
<<< {"status": "success", "message": "Properties set successfully"}
~~~

### 3. Start Streaming
~~~
>>> aletheia_start_stream(state)
<<< {"status": "success", "message": "Streaming started successfully"}
~~~

### 4. Send Data Frames (via `aletheia_send_frame`)

High-throughput streaming hot path. Each call passes a `struct aletheia_frame` with `can_id` 256, `extended` 0, `dlc` 8 and `data_len` 8; its BRS / ESI fields, left zero, encode absent CAN-FD metadata:
~~~
>>> aletheia_send_frame(state, &{timestamp: 100, data: [0xE8,0x03,0,0,0,0,0,0], ...})
<<< {"status": "ack"}

>>> aletheia_send_frame(state, &{timestamp: 200, data: [0xD0,0x07,0,0,0,0,0,0], ...})
<<< {"status": "ack"}

>>> aletheia_send_frame(state, &{timestamp: 300, data: [0x28,0x0A,0,0,0,0,0,0], ...})
<<< {"type": "property_batch", "results": [{"type": "property", "status": "holds", "property_index": 1}]}
~~~

The frames carry `Speed` 100, 200 and 260 km/h, so property 1 holds at the frame of timestamp 300 and leaves the stream.

### 5. End Streaming
~~~
>>> aletheia_end_stream(state)
<<< {"status": "complete", "results": [{"type": "property", "status": "holds", "property_index": 0}], "warnings": []}
~~~

Property 0 holds over the whole trace; property 1, answered at the frame of timestamp 300, is not answered again.

---

## Limits

Every parser at a trust boundary enforces explicit upper bounds on adversarial inputs. Rejection over the bound is a typed `InputBoundExceeded` error carrying the offending kind, the observed value, and the canonical limit it crossed.

The single source of truth is the Agda module `Aletheia.Limits` (`src/Aletheia/Limits.agda`). Python (`python/aletheia/limits.py`), Go (`go/aletheia/limits.go`) and C++ (`cpp/include/aletheia/limits.hpp`) mirror its kind codes and every limit but the per-field number limits (start bit, length, selector value, value-description key, attribute number, time bound), which the kernel alone decides; Rust (`rust/src/limits.rs`) mirrors the kind codes alone.

### Bound constants

| Bound | Limit | Kind code |
|---|---:|---|
| DBC text a binding reads (a file, or the text it sends to `parseDBCText`) | 64 MiB (67,108,864 bytes) | `input_length_bytes` |
| JSON command at the FFI boundary, in UTF-8 bytes | 64 MiB (67,108,864 bytes) | `input_length_bytes` |
| JSON nesting depth | 64 | `nesting_depth` |
| Messages per DBC file | 10,000 | `array_cardinality` |
| Signals per single message | 1,024 | `array_cardinality` |
| Attribute defs / assignments per file | 10,000 | `array_cardinality` |
| Value descriptions per file (`VAL_` + `VAL_TABLE_`) | 1,000,000 | `array_cardinality` |
| Comments per DBC file (`CM_`) | 10,000 | `array_cardinality` |
| Nodes per DBC file (`BU_`) | 10,000 | `array_cardinality` |
| Value tables per DBC file (`VAL_TABLE_` definitions) | 10,000 | `array_cardinality` |
| Signal groups per DBC file (`SIG_GROUP_`) | 10,000 | `array_cardinality` |
| Members of one signal group | 1,024 | `array_cardinality` |
| Environment variables per DBC file (`EV_`) | 10,000 | `array_cardinality` |
| `VAL_` lines naming no signal of the file | 10,000 | `array_cardinality` |
| Transmitters of one message (`senders`) | 10,000 | `array_cardinality` |
| Receivers of one signal | 10,000 | `array_cardinality` |
| Labels of one enumerated attribute type | 10,000 | `array_cardinality` |
| Selector values of one multiplexed signal (`multiplex_values`) | 1,024 | `array_cardinality` |
| LTL atoms per property | 1,024 | `atom_count` |
| Properties per `setProperties` call | 1,024 | `property_count` |
| DBC identifier length | 128 chars | `identifier_length` |
| DBC text field length (version, unit, comment, attribute name or value, value label) | 65,536 characters | `string_length` |
| Rational components of any number in a command or a DBC (\|numerator\| and denominator of the exact rational it denotes, reduced) | 340,282,366,920,938,463,463,374,607,431,768,211,455 (2¹²⁸ − 1) | `rational_component_magnitude` |
| A signal's start bit | 511 | `rational_component_magnitude` |
| A signal's length in bits | 512 | `rational_component_magnitude` |
| A selector value of a multiplexed signal (a `multiplex_values` element) | 2¹²⁸ − 1 | `rational_component_magnitude` |
| A value-description key (`VAL_`, `VAL_TABLE_`), in magnitude | 2¹²⁸ − 1 | `rational_component_magnitude` |
| An `INT`, `HEX` or `ENUM` attribute's value or bound, in magnitude | 9,223,372,036,854,775,807 (2⁶³ − 1) | `rational_component_magnitude` |
| A metric operator's time bound, in microseconds | 18,446,744,073,709,551,615 (2⁶⁴ − 1) | `rational_component_magnitude` |

Every number limit is decided on the parsed value, a rational's on its reduced components. The rational-component bound is one bound, decided in the kernel, for a JSON number anywhere in a request, a DBC literal and a decimal entered through `aletheia_parse_decimal` alike, so none of these admits a component another refuses and none carries one the C ABI's rational slots cannot: a `struct aletheia_rational` holds an unsigned 128-bit numerator and denominator beside a sign byte of its own, so the bound is symmetric in magnitude. The narrower number limits are decided on top of it, a DBC's by `checkBounds` and a time bound wherever one is read (a property, `aletheia_parse_time_bound`). The binary build and update entries take each signal value as a `struct aletheia_rational`, so every value they take is within the bound, and refuse a zero denominator with `parse_non_positive_denominator`.

An extracted signal value is held to the rational-component bound on both extraction paths, `aletheia_extract_signals` and `aletheia_extract_signals_bin`: a value whose reduced \|numerator\| or denominator is above 2¹²⁸ − 1 is refused per signal with `extraction_value_exceeds_wire_range`, the signal appearing in `errors` and not in `values`, so a 64-bit signal can produce a refusal even when every DBC field is in range. A violation's `timestamp` is the frame's `uint64_t`, at most 18446744073709551615; the kernel refuses a larger one with `parse_timestamp_past_wire` before it reads any other field of the frame.

A frame has no bound kind: `data_len` is a `uint8_t`, and the kernel refuses any payload whose length is not its DLC's byte count with `parse_payload_length_mismatch` (see [Binary Entry Points](#binary-entry-points)).

### Wire shape

`InputBoundExceeded` errors surface as the standard `{"status": "error", ...}` envelope with the consolidated code `input_bound_exceeded`. The `bound_kind` field in the structured payload discriminates which kind of bound was crossed, matching the `BoundKind` enum in `Aletheia.Limits`:

| Code | bound_kind values |
|---|---|
| `input_bound_exceeded` | `input_length_bytes` / `nesting_depth` / `array_cardinality` / `identifier_length` / `string_length` / `atom_count` / `property_count` / `rational_component_magnitude` |

The `message` field embeds the kind label, observed value, and limit; the structured `bound_kind` / `observed` / `limit` fields appear on the envelope alongside `code` and `message`, and a bound decided on a named part of the input adds `field`, the part that crossed it (`senders array`, `version string`, `signal factor`, `decimal`, `time bound`), or `line` and `column` for a name in a DBC text. Example:

~~~
<<< {"status": "error", "code": "input_bound_exceeded", "message": "nesting depth 65 exceeds limit 64", "bound_kind": "nesting_depth", "observed": 65, "limit": 64}
~~~

`observed` is the measured value up to 2¹²⁸ − 1, the top of the unsigned 128-bit range, which every binding's typed `observed` and `limit` hold. A measured value past that is reported as 340282366920938463463374607431768211455 and the message names no measured value, so a refusal never writes one of more than 39 digits however long the number that crossed the bound (kernel `Aletheia.Limits.saturateBound`), and every refusal at a limit of 2¹²⁸ − 1 reports the ceiling. The formatter writes `limit` through the same saturation, and `line`, `column`, `statement_line`, `statement_column`, `index`, `code_point` and `property_index` through `saturateObserved` at 2⁶⁴ − 1, which moves none of them: a limit is a constant, and a position, an index or a code point in an input within 64 MiB lies far below 2⁶⁴ − 1. The theorem `formatResponse-in-range` (`Aletheia.Protocol.ResponseFormat.Properties`) proves that every number, string and array any reply writes has the form `Aletheia.Protocol.ReplyRange` gives its place: a number within the range its `replyRange` row gives (a place with no row holds none), a string among the words its `replyText` row lists or not empty where the row asks it, an array a `replyNonEmpty` row names with at least one element; `formatResponse-readable` derives from it that every number has a numerator of magnitude at most 2¹²⁸ − 1 and a denominator at most 2¹²⁸ − 1, the range every binding's reader decodes. A command whose `"x"` is `1e39`:

~~~
<<< {"status": "error", "code": "input_bound_exceeded", "message": "rational component magnitude exceeds limit 340282366920938463463374607431768211455", "bound_kind": "rational_component_magnitude", "observed": 340282366920938463463374607431768211455, "limit": 340282366920938463463374607431768211455}
~~~

Both refusals above are decided on a command's whole JSON tree, after it is parsed and before it is dispatched, its nesting depth first and then its largest number component (`readParsed` in `Aletheia.Main.JSON`), so they carry no `field` and no command context, whichever part held the number: a `parseDBC` whose signal `factor` is 2¹²⁸ answers the reply above. The same factor in a DBC text, and a JSON number within 2¹²⁸ − 1 past a narrower limit, are refused where the DBC's bounds are decided, with `field` and the command context: `ParseDBCText: signal factor: rational component magnitude exceeds limit 340282366920938463463374607431768211455` with `field` `signal factor`, and for an `INT` attribute's maximum of 2⁶³ in a `parseDBC`, `ParseDBC: attribute maximum: rational component magnitude 9223372036854775808 exceeds limit 9223372036854775807` with `field` `attribute maximum`.

The DBC bounds (`array_cardinality`, `string_length` and `rational_component_magnitude` on a parsed DBC) are one decision shared by the four DBC commands, `parseDBC`, `parseDBCText`, `validateDBC` and `formatDBCText` (kernel `Aletheia.DBC.Bounds.checkBounds`), made before the command does anything else with the DBC. It refuses the first bound crossed, every count before any text, and the `message` names the offending field after the command context, e.g. `ParseDBCText: version string: string length 65546 exceeds limit 65536`. The structured `bound_kind` / `observed` / `limit` fields are the same on every command, so a binding decodes them with one typed handler. A DBC every command accepts carries the proof that it meets every bound, and loading requires it.

Every number in a DBC is held to its limit in the table above on both load routes, a JSON number past 2¹²⁸ − 1 refused before on the command's whole tree: after every count and text, `checkBounds` decides every signal's factor, offset, minimum, maximum, start bit, length, selector values and value-description keys, every environment variable's initial value and bounds, every numeric attribute bound and value (a `FLOAT` one at the rational-component bound), and every value-table and unresolved `VAL_` key, refusing the first past its limit with `rational_component_magnitude`, `observed` the larger reduced component (a key's magnitude), and `field` naming the position: `signal factor`, `signal offset`, `signal minimum`, `signal maximum`, `signal start bit`, `signal length`, `multiplex value`, `value description key`, `environment variable initial value`, `environment variable minimum`, `environment variable maximum`, `attribute minimum`, `attribute maximum`, `attribute value`, `value table key`, `unresolved value description key`. A start bit or a length past its frame is refused at parse, before the bounds, as `parse_signal_start_bit_exceeds_frame` or `parse_signal_bit_length_exceeds_frame`, since no frame holds more than 512 bits. A literal's digits are read by one core shared by the JSON and DBC grammars (kernel `Aletheia.DBC.DecRat.Literal`): it strips the significand's leading and trailing zeros and folds the digits only when the value can fit, holding a literal of 129 or more significant digits or digits before the decimal point, or of 128 or more after it, as a value with one component exactly 2¹²⁸, so reading a literal costs time linear in its length and the bound check after the parse refuses it, its message naming no measured value; a JSON exponent is compared by digit count before it is folded. No literal within the bound is held (`Aletheia.DBC.DecRat.Literal.Properties`), and the text round-trip theorem takes the bound every loaded DBC carries as its premise.

A DBC's texts are held to the DBC character set on both load routes, where its bounds are decided (`checkBounds`), and a DBC text is scanned before it is parsed: a string (version, unit, comment, value label, attribute enum label or string value) holds printable ASCII but `"` and `\`, plus TAB, LF and CR. A name is built only by the one identifier decision, as its characters are read: `[A-Za-z_][A-Za-z0-9_]*`, at most 128 characters (a character outside ASCII anywhere in the name is refused before its length, then the 129th character), not a DBC keyword; an attribute name, written between quotes, is an identifier too. The refusal is typed on both routes (`identifier_length`, `dbc_keyword_name`, `parse_invalid_identifier`, `dbc_invalid_character`), located by `field` in a parsed DBC and by `line` and `column` where the name starts in a DBC text (a character refusal at the character's own line and column). In a DBC text a name is read as far as its identifier characters go, so a word that starts with a character no identifier starts with is refused whole, while a character inside a name that no identifier holds ends the name and the statement fails at that character; a `"` or `\` in a string of a text passes the scan and is refused where the bounds are decided, with `field` and `index`.

`handler_validation_failed` errors (a `parseDBC` / `parseDBCText` rejected because the DBC has error-level validation issues) carry the **full structured issue list** on the envelope: errors *and* warnings, in the same `{severity, code, detail}` element shape as the `validation` response, plus the same `has_errors` flag (trivially `true` on this path; included so both payloads decode with one issue decoder). The `message` field flattens only the error-level details. Example:

~~~
<<< {"status": "error", "code": "handler_validation_failed", "message": "ParseDBCText: validation failed: Message 'M': duplicate signal name 'S'", "has_errors": true, "issues": [{"severity": "error", "code": "duplicate_signal_name", "detail": "Message 'M': duplicate signal name 'S'"}, {"severity": "warning", "code": "offset_scale_range", "detail": "Message 'M', signal 'S': its bits carry values above the declared maximum"}]}
~~~

Text parse errors, of a `.dbc` text or of a decimal entered through `aletheia_parse_decimal`, carry **byte-exact failure positions** on the envelope. The parser tracks a *furthest-failure watermark*: the deepest position any parse attempt reached (`<|>` alternatives merge their failed arms' depths; `many` keeps the depth of the element attempt it swallowed), so the reported byte is the first character no grammar rule could accept, not merely the start of the offending statement.

- `text_parse_failure` exposes structured `line` / `column` (the watermark).
- `text_trailing_input` exposes `line` / `column` (the watermark, inside the first unparseable statement) **plus** `statement_line` / `statement_column` (where that statement starts, the first unconsumed byte).
- `dispatch_invalid_json` exposes `line` / `column` (the JSON parser shares the same combinators and watermark).

### Two-layer enforcement

Per AGENTS.md universal rule "Adversarial-input bounds at parser surfaces", bounds are enforced in two layers:

1. **Agda kernel**, definitive: every bound of the table but the DBC text's, which bounds what a binding reads, is decided inside the verified core, at the parser entry or on the parsed value, and the typed `InputBoundExceeded` error flows out via the protocol `Response`.
2. **Binding**, short-circuit: Python (`aletheia.InputBoundExceededError`), Go (`*aletheia.InputBoundExceededError`) and C++ (`aletheia::InputBoundExceededError`, the `bound_info()` of an `AletheiaError`) refuse a JSON command past `max-json-bytes` and a DBC text past `max-dbc-text-bytes` before marshaling it across the FFI boundary, so a 100 MB JSON does not allocate buffers in the binding before being rejected. Rust sends every JSON command and DBC text to the kernel as it is and types the kernel's refusal as `Error::InputBoundExceeded(Box<BoundRefusal>)`.

The two layers agree on every limit a binding mirrors: `tools/check_limits_parity.py` (`cabal run shake -- check-limits-parity`, a `tools/run_ci.py` gate) fails on a mirrored constant or kind code that differs from `Aletheia.Limits`, and on a mirror of a limit the kernel alone decides.

### Updating bounds

Bounds are intentionally generous (commercial automotive DBCs are 1-10 MiB, ~6× headroom). If your inputs legitimately exceed a bound:

1. Surface the bound and the legitimate input size in an issue or PR.
2. Update `Aletheia.Limits.max-*` (single source of truth).
3. Mirror the constant in the Python, Go and C++ limits files, unless the kernel alone decides it.
4. Update this table.

---

## Error Handling

### Common Errors

Each example is the kernel's reply to the command named, verbatim.

**Invalid JSON** (`{"type": "command", "command": }`):
~~~
<<< {"status": "error", "code": "dispatch_invalid_json", "message": "invalid JSON: parse failed at line 1, column 32", "line": 1, "column": 32}
~~~

**Missing Required Field** (`{"type": "command"}`):
~~~
<<< {"status": "error", "code": "route_missing_command_field", "message": "missing 'command' field"}
~~~

**Unknown Command** (`{"type": "command", "command": "startStream"}`; streaming has no JSON command form, see [Binary Entry Points](#binary-entry-points)):
~~~
<<< {"status": "error", "code": "route_unknown_command", "message": "unknown command 'startStream'"}
~~~

**No DBC Loaded** (`setProperties` before `parseDBC`):
~~~
<<< {"status": "error", "code": "handler_no_dbc", "message": "SetProperties: DBC not loaded"}
~~~

### Error Code Reference

Every error reply carries a stable `code` beside its `message`, drawn from `src/Aletheia/Error.agda`, or `ffi_validation_error` when the shared library refuses an argument it cannot read or a result it cannot write; [`docs/WIRE_CODES.yaml`](../WIRE_CODES.yaml) lists every code (`tools/check_wire_codes.py`). Tooling switches on `code`; `message` is text for a reader.

Codes are grouped by domain: `parse_*` (JSON/DBC parsing), `extraction_*` (signal extraction), `frame_*` (frame building/update), `route_*` (command dispatch), `handler_*` (stream state machine), `dispatch_*` (top-level request routing), `text_*` (parse of a `.dbc` text or of a decimal), `dbc_text_*` (DBC attribute refinement); `input_bound_exceeded`, `dbc_invalid_character` and `dbc_keyword_name`, which refuse a bound, a character or a name wherever an input is read, are listed with the parse errors. A context the message opens with leaves the code the innermost error's: `validateDBC` refusing a message's DLC answers `parse_invalid_dlc_bytes` with the message `ValidateDBC: message 'M': DLC 15 is not a valid CAN byte count`.

#### Parse errors: malformed DBC or property JSON, or a binary entry's frame

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
| `parse_invalid_dlc_bytes` | DLC byte count is not a valid CAN/CAN-FD length | `dlc` is the byte count, one of 0 to 8, 12, 16, 20, 24, 32, 48 or 64 |
| `parse_root_not_object` | Top-level JSON is not an object | Wrap the request in `{...}` |
| `parse_missing_signal_name` | Signal object has no `name` | Add `"name": "..."` |
| `parse_signal_bit_length_zero` | Signal `length` is zero | Must be `≥ 1` |
| `parse_signal_start_bit_exceeds_frame` | Signal `startBit` lies outside the message's frame capacity | Must be below 8 × the message's byte count |
| `parse_signal_bit_length_exceeds_frame` | Signal `length` exceeds the message's frame capacity | Must be at most 8 × the message's byte count |
| `parse_signal_big_endian_overflow` | Big-endian signal's descending bit run extends past the end of the frame | The Motorola `startBit` names the MSB; `length` bits must fit below it within the frame |
| `parse_invalid_kind` | An enum-like string field carries an unrecognised value (`invalid <domain> kind '<value>'`) | Use one of the documented values for that field |
| `parse_non_terminating_rational` | A rational field is non-terminating in decimal (denominator has a prime factor outside {2, 5}) | Use a value representable as a terminating decimal |
| `parse_invalid_identifier` | A name is not a DBC identifier (a letter or `_`, then letters, digits and `_`); `field` locates it in a parsed DBC or a property, `line` and `column` where the name starts in a DBC text, where a name is read as far as its identifier characters go (`S-x` is the name `S` followed by text the statement refuses) | Fix the identifier name |
| `dbc_invalid_character` | A character outside the DBC character set: a string holds printable ASCII but `"` and `\`, plus TAB, LF and CR; a name holds ASCII (an ASCII character outside the identifier grammar is `parse_invalid_identifier`). `code_point` names it; `field` and `index` locate it where a DBC's bounds are decided (a parsed DBC, or a `"` or `\` in a text's string), `line` and `column` where a DBC text's scan finds a character outside printable ASCII, TAB, LF and CR | Replace the character; a `.dbc` file is read byte for byte, so a byte above 0x7E is refused whatever the file's encoding |
| `dbc_keyword_name` | A DBC keyword used as a name: a section keyword (`VERSION`, `NS_`, `BS_`, `BU_`, `BO_`, `SG_`, `EV_`, `CM_`), a symbol of the `NS_` block, or an attribute type word (`INT`, `HEX`, `FLOAT`, `STRING`, `ENUM`); the whole list is `dbcKeywords` in `src/Aletheia/DBC/Identifier.agda`. `keyword` carries it, with `field` in a parsed DBC or a property, with `line` and `column` where the name starts in a DBC text | Rename |
| `input_bound_exceeded` | An input crossed one of the kernel's bounds: `bound_kind` names it, `observed` and `limit` carry the measured value and the limit, a measured value past 2¹²⁸ − 1 written as 2¹²⁸ − 1 and named by no number in the message; `field`, or `line` and `column`, locate a bound decided on a named part | Keep the input within the bound: [§ Limits](#limits) lists each one, [§ Wire shape](#wire-shape) the fields |
| `parse_non_natural_field` | A field is present but its value is not a JSON natural number | Supply a non-negative integer |
| `parse_dlc_code_out_of_range` | A binary entry's frame has a DLC above 15 | Encode the DLC as a code `0-15` |
| `parse_payload_length_mismatch` | A binary entry's frame has a `data_len` that is not its DLC's byte count | Send exactly `dlcToBytes(dlc)` bytes |
| `parse_payload_byte_out_of_range` | A binary entry's payload byte is 256 or above | Unreachable through `aletheia.h`'s `uint8_t` payload |
| `parse_non_positive_denominator` | A signal value for a build or an update has a zero or negative denominator | Give each value a positive denominator |
| `parse_signal_array_length_mismatch` | A build's or an update's signal-value arrays differ in length | Unreachable through `struct aletheia_signal_values`, which carries one count |
| `parse_timestamp_past_wire` | A frame, error or remote entry's timestamp is above 18446744073709551615 | Unreachable through `struct aletheia_frame`, whose `timestamp` is a `uint64_t` |

#### Extraction errors: signal extraction on a data frame

| Code | Meaning | Likely cause / fix |
|---|---|---|
| `extraction_mux_value_mismatch` | Multiplexor value in frame does not select this signal | Never in `errors`: extraction lists the signal in `absent` |
| `extraction_mux_signal_not_found` | Named multiplexor signal missing from message definition | Fix the DBC |
| `extraction_mux_chain_cycle` | The multiplexor chain is longer than the message's signals, so it holds a cycle | Unreachable for a loaded DBC, which `multiplexor_cycle` refuses at load |
| `extraction_mux_extraction_failed` | Failed to read the multiplexor signal's own bits | Check the multiplexor signal's `startBit`/`length` |
| `extraction_value_exceeds_wire_range` | The extracted exact value's reduced numerator magnitude or denominator is above 2¹²⁸ − 1, the rational component bound; the kernel refuses the value on both extraction paths, the signal in `errors` with the reason `extracted value's numerator or denominator magnitude exceeds 340282366920938463463374607431768211455` | Per-signal runtime condition, not a DBC defect: the exact value can pass the bound though every DBC number and frame byte is within it (a `factor` of 1/2¹²⁷ and an `offset` of 1/5⁵⁵ give raw 1 the denominator 2¹²⁷ × 5⁵⁵); rescale the signal's `factor`/`offset` if the exact value must travel |
| `extraction_signal_past_frame_end` | The signal's last bit lies past the end of the frame that arrived; the reason names the frame's byte count | Send the frame at the byte count the DBC declares for its message |

#### Frame errors: binary build/update paths (`aletheia_build_frame_bin` / `aletheia_update_frame_bin`)

| Code | Meaning | Likely cause / fix |
|---|---|---|
| `frame_signal_not_found` | Named signal not in the target message | Check the signal name against the DBC |
| `frame_signal_index_oob` | A build's or an update's signal index is past the target message's signals | Pass a position in the message's signal list, as each binding resolves a signal's name |
| `frame_value_out_of_range` | A requested value lies outside the signal's `[minimum, maximum]` | Clip at the caller, or widen the DBC's range within what the bits carry |
| `frame_value_not_representable` | No integer raw value scales to the requested value under the signal's factor and offset | Request a value on the signal's grid, `offset + k × factor` for an integer `k` |
| `frame_signals_overlap` | Two signals requested by one build or update occupy overlapping bits | Request only one signal per bit range, or fix the DBC |
| `frame_signal_past_frame_end` | A signal's last bit lies past the end of the frame (the build's DLC, or the updated frame's) | Use a DLC whose byte count holds every signal of the message |
| `frame_can_id_not_found` | `canId` not present in loaded DBC | Re-check the CAN ID against the DBC |
| `frame_can_id_mismatch` | Request `canId` does not match the frame being updated | For the binary update path, the existing frame's ID must match |
| `frame_signal_value_out_of_bounds` | An extracted value lies outside the signal's `[minimum, maximum]` | Not a build or update refusal: its message is the reason extraction reports for the signal |

#### Route errors: command dispatch

| Code | Meaning | Likely cause / fix |
|---|---|---|
| `route_missing_field` | `parseDBCText` has no `text` string | Add `"text": "..."` |
| `route_unknown_command` | `command` value not recognised | See the Commands section for the valid commands |
| `route_missing_command_field` | Request has no `command` field | Add `"command": "..."` |
| `route_missing_dbc_field` | `parseDBC`, `validateDBC` or `formatDBCText` has no `dbc` field | Add the `dbc` object |
| `route_missing_props_field` | `setProperties` has no `properties` array | Add `"properties": [...]` |

#### Handler errors: stream state machine

| Code | Meaning | Likely cause / fix |
|---|---|---|
| `handler_no_dbc` | Operation requires a loaded DBC | Call `parseDBC` or `parseDBCText` first |
| `handler_already_streaming` | `aletheia_start_stream` while already streaming | Call `aletheia_end_stream` before restarting |
| `handler_not_streaming` | `aletheia_end_stream` outside a stream | Streaming must be active to end it |
| `handler_stream_not_started` | A data frame with a DBC loaded but no stream started | Call `aletheia_start_stream` before `aletheia_send_frame` |
| `handler_stream_active` | `setProperties` while a stream is active | End the stream first |
| `handler_property_parse_failed` | A property of the `setProperties` list is no property; the message names its position and the reason (`SetProperties: property 0: field 'formula' is missing`) | Fix the field the reason names, against the [LTL Property Format](#ltl-property-format) |
| `handler_property_refused` | A property or a time bound checked on its own, by `aletheia_check_property` or `aletheia_parse_time_bound`, was refused; the message is the reason alone | Fix the field the reason names |
| `handler_unknown_signal` | A property names a signal no signal of the loaded DBC carries; the message names it | Name a signal of the DBC |
| `handler_validation_failed` | A DBC to load has an error-level validation issue | The envelope's `issues` array carries every issue, errors and warnings (see [§ Wire shape](#wire-shape)) |
| `handler_text_roundtrip_failed` | `formatDBCText` refused: the emitted `.dbc` text does not re-parse to the input DBC | The DBC cannot be written as round-tripping `.dbc` text (a multi-value multiplexed signal, for one); the envelope's `issues` array is led by the error-severity `text_roundtrip_divergence` (see [FormatDBCText](#formatdbctext)) |
| `handler_non_monotonic_timestamp` | A data, error or remote frame's timestamp is below the previous one's in the stream | Sort frames by timestamp before streaming: metric LTL operators require monotonic timestamps |

#### Dispatch errors: top-level request routing

| Code | Meaning | Likely cause / fix |
|---|---|---|
| `dispatch_missing_type_field` | Request has no `type` field | Add `"type": "command"` |
| `dispatch_unknown_message_type` | `type` value not recognised | Only `command` is supported |
| `dispatch_invalid_json` | Request was not valid JSON (structured `line`/`column` mark the first unparseable byte) | Validate the JSON before sending |
| `dispatch_request_not_object` | Top-level value is not an object | Wrap in `{...}` |

#### Text parse errors: `parseDBCText` / `formatDBCText` / `aletheia_parse_decimal`

| Code | Meaning | Likely cause / fix |
|---|---|---|
| `text_parse_failure` | A text could not be parsed, a `.dbc` text or a decimal entered through `aletheia_parse_decimal` (structured `line`/`column` mark the deepest byte any parse attempt reached) | Check the file against the DBC grammar, or the literal against the decimal grammar, at the reported byte; run `validate` for structural issues |
| `text_trailing_input` | The parse stopped at the first unparseable statement of a `.dbc` text, or at the unconsumed tail of a decimal: structured `line`/`column` mark the exact failing byte inside it, `statement_line`/`statement_column` where the statement starts | Fix the statement or the literal at the reported byte |
| `dbc_text_attribute_refinement_failed` | A `BA_DEF_DEF_` / `BA_` / `BA_REL_` entry failed refinement: the message names the offending attribute and whether it is undeclared or its value does not fit the declared type | Declare the attribute via `BA_DEF_` first; keep values inside the declared type (e.g. `ENUM` indices in range) |

A signal-geometry refusal on the text route carries the JSON route's `parse_signal_*` code and names the signal (`signal 'NAME': ...`) in place of a `line`/`column` position, the gate running after the `SG_` line parses (see [ParseDBC](#parsedbc)).

#### The library's own refusal: an argument it cannot read, a result it cannot write

| Code | Meaning | Likely cause / fix |
|---|---|---|
| `ffi_validation_error` | The shared library refused an argument it cannot read (a NULL pointer, a size past what the library can index, a text that is not UTF-8 or holds a NUL byte) or a result it cannot write (a buffer smaller than the frame the kernel built); the message names which | Pass what the entry's header documents: a text as its UTF-8 bytes without NUL, buffers at the frame's size |

---

## Implementation Notes

### FFI Entry Points
- **Commands**: JSON text via `aletheia_process(state, &text)`, the text being its UTF-8 bytes and their count in one `struct aletheia_text`
- **Stream and frames**: `aletheia_start_stream`, `aletheia_end_stream`, `aletheia_send_frame` (the streaming hot path), `aletheia_send_error`, `aletheia_send_remote`, `aletheia_extract_signals` and `aletheia_format_dbc`, each answering a JSON string
- **Binary output**: `aletheia_build_frame_bin`, `aletheia_update_frame_bin` and `aletheia_extract_signals_bin`, into a `struct aletheia_buffer`
- **Text entries**: `aletheia_parse_decimal`, `aletheia_parse_time_bound` and `aletheia_check_property`, each into its own result structure, and `aletheia_format_rational`, answering a string
- **Lifecycle**: `hs_init` once per process, before any `aletheia_*` call but `aletheia_abi_version`; `aletheia_init` and `aletheia_close` for a session; `aletheia_allocated_bytes`; `aletheia_free_str` for every returned string and `err`, `aletheia_free_buf` for an extraction's buffer
- Each call carries one complete message, with no newline delimiter
- State is managed via `StablePtr (IORef StreamState)` on the Haskell side

### Sequential Processing
- Each call runs to completion before it returns
- One session handle is used from one thread at a time; different handles may be used from different threads
- A data, error or remote frame answers `ack`, a property batch or a refusal

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

The event vocabulary is [`docs/LOG_EVENTS.yaml`](../LOG_EVENTS.yaml), each event's name, level and meaning, and each binding's parity test holds its events to it; this section groups the events by category.

All four bindings share that vocabulary, so a single downstream log pipeline can consume any of them (Python `logging`, C++ `Logger` callback, Go `slog`, Rust `Logger` trait). Python, C++ and Go emit every event of it; the Rust binding defines every event and emits all but the three `cache.*` events, which instrument an extraction cache that binding does not implement (see `rust/src/log.rs`).

| Category | Level | Events |
|---|---|---|
| Lifecycle | INFO (`rts.cores_mismatch` is WARNING) | `dbc.parsed`, `properties.set`, `stream.started`, `stream.ended`, `rts.cores_mismatch` |
| Frame processing | DEBUG | `frame.processed`, `error_event.sent`, `remote_event.sent` |
| Extraction cache | DEBUG / WARNING | `cache.hit`, `cache.miss`, `cache.full` |
| Extraction errors | WARNING | `extraction.process_failed`, `extraction.parse_failed` |
| End-of-stream diagnostics | WARNING | `endstream.uncached_atom` |

Each record carries the event name plus structured key/value fields (frame count, property index, reason string, etc.). Per-binding definitions are `python/aletheia/client/_log.py` (`LogEvent` enum), `cpp/src/client.cpp` and `client_stream.cpp` (inline event literals at the emit sites), `go/aletheia/client.go`, `client_stream.go`, `client_enrich.go` and `runtime_start.go` (slog emission sites), and `rust/src/log.rs` (`events::*` constants + `events::ALL`). Adding a new event follows the steps `docs/LOG_EVENTS.yaml` lists, and this table; the Rust parity test (`rust/tests/log_events.rs`) pins `events::ALL` to [`docs/LOG_EVENTS.yaml`](../LOG_EVENTS.yaml) bijectively, so a new YAML row without the matching Rust constant fails CI even if Rust never emits the event.

See [INTERFACES.md § Structured Logging](../reference/INTERFACES.md#structured-logging) for per-binding wiring examples.

---

## See Also

- [DESIGN.md](DESIGN.md) - Overall architecture and design decisions
- [PROJECT_STATUS.md](../../PROJECT_STATUS.md) - Phase completion status and milestones
- [PYTHON_API.md](../reference/PYTHON_API.md) - Python client library
