# CLI Reference

**Purpose**: Command-line interface for Aletheia CAN signal verification.
**Version**: 1.1.1
**Last Updated**: 2026-04-15

---

## Overview

```
python3 -m aletheia <subcommand> [options]
```

Five subcommands: `check`, `validate`, `extract`, `signals`, `mux-query`.

**Exit codes** (all subcommands):
- `0` — success (or all checks passed)
- `1` — violations found (`check`) or validation failed (`validate`)
- `2` — error (bad arguments, missing files, parse failures)

---

## check

Run LTL checks against a CAN log file.

```
python3 -m aletheia check [--dbc FILE] [--checks FILE] [--excel FILE] [--json] LOGFILE
```

**Arguments**:

| Argument | Required | Description |
|----------|----------|-------------|
| `LOGFILE` | yes | CAN log file (.asc, .blf, .csv, .db, .log, .mf4, .trc; .gz compressed supported) |
| `--dbc FILE` | \* | .dbc file (or .xlsx with DBC sheet) for signal definitions |
| `--checks FILE` | \* | .yaml or .xlsx file with check definitions |
| `--excel FILE` | \* | .xlsx workbook containing both DBC and Checks sheets |
| `--defaults FILE` | no | .yaml or .xlsx file with default checks (prepended before session checks) |
| `--json` | no | Output results as JSON |

\* At least one DBC source (`--dbc` or `--excel`) and one checks source (`--checks` or `--excel`) required.

**Text output**:
```
Aletheia — CAN Signal Verification

DBC:    vehicle.dbc
Checks: checks.yaml (3 checks)
Log:    drive.blf

Streaming 12450 frames...

RESULT: 2 violations found

  1. [t=4523.000ms] Speed limit (safety)
     VehicleSpeed = 225.5 (formula: always(VehicleSpeed < 220))

  2. [t=8100.500ms] Brake response (safety)
     BrakePressure = 0 (formula: always(BrakePressure > 0))

Summary: 2 violations in 3 checks, 12450 frames processed
```

**JSON output** (`--json`):
```json
{
  "status": "violations",
  "total_frames": 12450,
  "total_violations": 2,
  "violations": [
    {
      "check_index": 0,
      "check_name": "Speed limit",
      "severity": "safety",
      "timestamp_us": 4523000,
      "reason": "Always violated",
      "signal_name": "VehicleSpeed",
      "actual_value": 225.5,
      "condition": "always(VehicleSpeed < 220)"
    }
  ]
}
```

Enriched fields (`signal_name`, `actual_value`, `condition`) are populated when check diagnostics are available.

---

## validate

Validate a DBC definition for structural issues (overlapping signals, zero-length signals, etc.).

```
python3 -m aletheia validate [--dbc FILE] [--excel FILE] [--json]
```

**Arguments**:

| Argument | Required | Description |
|----------|----------|-------------|
| `--dbc FILE` | \* | .dbc file (or .xlsx with DBC sheet) |
| `--excel FILE` | \* | .xlsx workbook with DBC sheet |
| `--json` | no | Output as JSON |

\* At least one of `--dbc` or `--excel` required.

**Text output** (issues found):
```
Validation FAILED: 2 errors, 1 warnings

  1. [ERROR] signal_overlap: Signals 'Speed' and 'RPM' overlap in message 'EngineData'
  2. [ERROR] bit_length_zero: Signal 'Unused' has zero bit length in message 'Status'
  3. [WARNING] empty_message: Message 'Empty' has no signals defined

```

**Text output** (no issues):
```
Validation passed: no issues found
```

**JSON output** (`--json`):
```json
{
  "status": "fail",
  "has_errors": true,
  "total_issues": 3,
  "issues": [
    {"severity": "error", "code": "signal_overlap", "detail": "Signals 'Speed' and 'RPM' overlap in message 'EngineData'"},
    {"severity": "error", "code": "bit_length_zero", "detail": "Signal 'Unused' has zero bit length in message 'Status'"},
    {"severity": "warning", "code": "empty_message", "detail": "Message 'Empty' has no signals defined"}
  ]
}
```

**Exit codes**:
- `0` — validation passed (no errors; warnings are OK)
- `1` — validation failed (at least one error)

---

## extract

Decode signals from a single CAN frame.

```
python3 -m aletheia extract --dbc FILE CAN_ID DATA
```

**Arguments**:

| Argument | Required | Description |
|----------|----------|-------------|
| `CAN_ID` | yes | CAN ID as hex (`0x100`) or decimal (`256`) |
| `DATA` | yes | Frame data as hex (see formats below) |
| `--dbc FILE` | yes | .dbc or .xlsx file |
| `--json` | no | Output as JSON |

**Hex data formats** (all equivalent):
```
401F7D0000000000
40 1F 7D 00 00 00 00 00
40:1F:7D:00:00:00:00:00
0x401F7D0000000000
```

**Text output**:
```
CAN ID 0x100 (EngineData):

  EngineSpeed          = 2000.0 rpm
  EngineTemp           = 85.0 C

Errors: none
Absent: none
```

**JSON output** (`--json`):
```json
{
  "can_id": 256,
  "values": {"EngineSpeed": 2000.0, "EngineTemp": 85.0},
  "errors": {},
  "absent": []
}
```

---

## signals

List all signals defined in a DBC file.

```
python3 -m aletheia signals [--dbc FILE] [--excel FILE] [--json]
```

**Arguments**:

| Argument | Required | Description |
|----------|----------|-------------|
| `--dbc FILE` | \* | .dbc file |
| `--excel FILE` | \* | .xlsx workbook with DBC sheet |
| `--json` | no | Output as JSON (full DBC definition) |

\* At least one of `--dbc` or `--excel` required.

**Text output**:
```
Message 0x100 EngineData (DLC 8, sender ECU)
  EngineSpeed          bits[0:16]   LE  unsigned    x0.25 +0     rpm  [0, 8000]
  EngineTemp           bits[16:8]   LE  unsigned    x1 -40         C  [-40, 215]

Message 0x200 BrakeStatus (DLC 8, sender ECU)
  BrakePressure        bits[0:16]   LE  unsigned    x0.1 +0      bar  [0, 6553.5]

2 messages, 3 signals
```

---

## Input Formats

### CAN Log Files

Supported via [python-can](https://python-can.readthedocs.io/):

| Extension | Format |
|-----------|--------|
| `.asc` | Vector ASCII |
| `.blf` | Vector Binary Logging Format |
| `.csv` | Comma-separated values |
| `.db` | SQLite database |
| `.log` | candump log |
| `.mf4` | ASAM MDF4 |
| `.trc` | PEAK TRC |

---

## mux-query

Inspect the multiplexor structure of a DBC message.

```
python3 -m aletheia mux-query [--dbc FILE] [--excel FILE] [--extended] [--mux NAME --value N] [--json] MESSAGE
```

`MESSAGE` is a CAN ID (hex `0x100` or decimal `256`) or a message name.

**Options**:

| Option | Description |
|--------|-------------|
| `--dbc FILE` | `.dbc` file |
| `--excel FILE` | `.xlsx` workbook with DBC sheet |
| `--extended` | Treat CAN ID as 29-bit extended (default: 11-bit standard) |
| `--mux NAME` | Multiplexor signal name (requires `--value`) |
| `--value N` | Multiplexor value (requires `--mux`) |
| `--json` | Output as JSON |

**Without `--mux`/`--value`**: prints a summary of all multiplexors and their values for the message.

**With `--mux`/`--value`**: lists the signals active when the named multiplexor has the given value.

**Examples**:

```bash
# Show multiplexor structure for message 0x100
python3 -m aletheia mux-query --dbc vehicle.dbc 0x100

# List signals when multiplexor "Mode" has value 5
python3 -m aletheia mux-query --dbc vehicle.dbc 0x100 --mux Mode --value 5

# JSON output
python3 -m aletheia mux-query --dbc vehicle.dbc 0x100 --json
```

---

## Common Options

Error frames and remote frames are skipped by default. Frame data is normalized to match the DLC byte count (padded or truncated as needed).

### DBC Sources

- `.dbc` — standard Vector DBC file (parsed by cantools)
- `.xlsx` — Excel workbook with a DBC sheet (see [Interface Guide](INTERFACES.md#excel-loader))

### Check Sources

- `.yaml` — YAML check definitions (see [Interface Guide](INTERFACES.md#yaml-loader))
- `.xlsx` — Excel workbook with Checks and When-Then sheets (see [Interface Guide](INTERFACES.md#excel-loader))

---

## See Also

- **[Interface Guide](INTERFACES.md)** — Check API, YAML, Excel loader reference
- **[Python API Guide](PYTHON_API.md)** — Full DSL and AletheiaClient reference
- **[Quick Start](../guides/QUICKSTART.md)** — 5-minute tutorial
