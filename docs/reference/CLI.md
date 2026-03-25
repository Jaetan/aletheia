# CLI Reference

**Purpose**: Command-line interface for Aletheia CAN signal verification.
**Last Updated**: 2026-03-19

---

## Overview

```
python -m aletheia <subcommand> [options]
```

Four subcommands: `check`, `validate`, `extract`, `signals`.

**Exit codes** (all subcommands):
- `0` — success (or all checks passed)
- `1` — violations found (`check`) or validation failed (`validate`)
- `2` — error (bad arguments, missing files, parse failures)

---

## check

Run LTL checks against a CAN log file.

```
python -m aletheia check [--dbc FILE] [--checks FILE] [--excel FILE] [--json] LOGFILE
```

**Arguments**:

| Argument | Required | Description |
|----------|----------|-------------|
| `LOGFILE` | yes | CAN log file (.asc, .blf, .csv, .log, .mf4, .trc; .gz compressed supported) |
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
     Always violated

  2. [t=8100.500ms] Brake response (safety)
     Always violated

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
      "condition": "never_exceeds(220)"
    }
  ]
}
```

Enriched fields (`signal_name`, `actual_value`, `condition`) are populated when check diagnostics are available.

---

## validate

Validate a DBC definition for structural issues (overlapping signals, zero-length signals, etc.).

```
python -m aletheia validate [--dbc FILE] [--excel FILE] [--json]
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

  1. [ERROR] OVERLAP: Signals 'Speed' and 'RPM' overlap in message 'EngineData'
  2. [ERROR] ZERO_LENGTH: Signal 'Unused' has zero bit length in message 'Status'
  3. [WARNING] NO_SIGNALS: Message 'Empty' has no signals defined

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
  "total_issues": 2,
  "issues": [
    {
      "severity": "error",
      "code": "OVERLAP",
      "detail": "Signals 'Speed' and 'RPM' overlap in message 'EngineData'"
    }
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
python -m aletheia extract --dbc FILE CAN_ID DATA
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
401F820000000000
40 1F 82 00 00 00 00 00
40:1F:82:00:00:00:00:00
0x401F820000000000
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
python -m aletheia signals [--dbc FILE] [--excel FILE] [--json]
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
  EngineTemp           bits[16:8]   LE  signed      x1 -40         C  [-40, 215]

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
| `.log` | candump log |
| `.mf4` | ASAM MDF4 |
| `.trc` | PEAK TRC |

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
