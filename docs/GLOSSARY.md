# Glossary

Plain-language definitions of the CAN, DBC, and verification terms used across the Aletheia docs. Written for technicians and test engineers — no programming background assumed. Where one of these terms first appears in another guide, it links back here, so you can always follow the word to a one-sentence explanation.

---

## CAN and the bus

**CAN (Controller Area Network)** — the standard wiring-and-messaging system that lets the electronic control units (ECUs) in a vehicle or machine talk to each other over one shared pair of wires.

**CAN bus** — the shared two-wire connection itself: every ECU listens to it all the time and takes turns transmitting on it.

**CAN frame** — one message on the bus: an identifier plus a small block of data bytes (up to 8 on classic CAN, up to 64 on CAN-FD), broadcast so every ECU can hear it.

**Arbitration ID** (also called *CAN ID* or *message ID*) — the number at the front of every frame that both says what the message is about and decides who wins when two ECUs transmit at once (the lower the number, the higher the priority).

**11-bit (standard) vs 29-bit (extended) ID** — two sizes of arbitration ID: the original 11-bit form gives about 2,000 distinct IDs, while the 29-bit "extended" form gives hundreds of millions for networks that need more; any given frame is one or the other, and Aletheia tracks which.

**DLC (Data Length Code)** — how many data bytes the frame carries: 0–8 for classic CAN, or a coded value that reaches up to 64 bytes for CAN-FD.

---

## CAN-FD (the faster, bigger variant)

**CAN-FD (CAN with Flexible Data-rate)** — a newer version of CAN that carries more data per frame (up to 64 bytes instead of 8) and can send the data portion at a higher bit rate.

**BRS (Bit Rate Switch)** — a flag inside a CAN-FD frame that says "the data part of this frame was sent at the faster rate"; it only exists on CAN-FD frames.

**ESI (Error State Indicator)** — a flag inside a CAN-FD frame reporting whether the transmitting ECU currently considers itself healthy ("error-active") or degraded ("error-passive").

---

## Describing signals: the DBC

**DBC** — the database file (`.dbc`) that describes what each CAN message *means*: which ID carries which signals, and how to turn the raw bytes into real-world values.

**Signal** — one named physical quantity packed inside a frame's bytes (for example `VehicleSpeed` or `CoolantTemp`) that the DBC tells you how to read out.

**Start-bit** — where inside the frame's bytes a signal's bits begin; combined with the signal's length, it pins down exactly which bits to read.

**Byte-order (endianness)** — whether a multi-byte signal is stored most-significant-byte first ("big-endian" / Motorola) or least-significant-byte first ("little-endian" / Intel); reading it the wrong way round yields a wrong value.

**Factor and offset** — the two numbers that convert a signal's raw integer into its real-world value using `physical = raw × factor + offset` (for example, raw `4010 × 0.01 + 0 = 40.10 °C`).

**Multiplexed signals** — several different signals that share the same bits of a message at different times, with one "multiplexor" field in the frame stating which signal those bits currently represent.

**Well-formed DBC** — a DBC that satisfies the structural conditions a given guarantee assumes. Aletheia uses two distinct senses, and they are not the same: *validator-clean* (`aletheia validate` reports no errors — the precondition of the decoding and checking guarantees) and *text-round-trip well-formed* (a stricter nine-condition class, `WellFormedTextDBCAgg` in the proofs, that the "export to `.dbc` text, parse it back, get the original" guarantee assumes). A DBC can validate clean and still fall outside the second class — for example one using multi-value multiplexing, which today exports lossily.

---

## Recordings: traces and log files

**Trace** — a recording of CAN bus traffic: a time-ordered list of the frames that appeared on the bus, saved to a file so it can be replayed or analysed later.

**`.blf`** — Vector Binary Logging Format: the compact binary trace file written by Vector's CANoe / CANalyzer tools (the preferred format — smallest and most time-precise).

**`.asc`** — Vector ASCII: a plain-text trace file, also from CANoe / CANalyzer, that you can open in an ordinary text editor.

**`.mf4`** — ASAM MDF4: the measurement-data trace format written by dSPACE, ETAS, Vector, and Silver test benches.

**candump `.log`** — the plain-text trace format written by the Linux `candump` tool (from `can-utils`) when capturing directly from a SocketCAN interface; Aletheia reads it natively, with no conversion step.

---

## How Aletheia checks

**LTL (Linear Temporal Logic)** — a precise way of writing rules about how values behave *over time* — "speed never exceeds 220", or "when the brake is pressed the brake light must come on within 100 ms" — in a form a computer can check against a trace exactly.

**Formal verification / "formally verified"** — mathematically *proven* correct, not merely tested on examples: Aletheia's checking core ships with machine-checked proofs (written in the Agda proof language) that it does what it claims, so a bug in that core cannot slip through the way one can with testing alone.

---

## Under the hood

**FFI (Foreign Function Interface)** — the bridge that lets a program written in one language call code written in another; Aletheia's verified core is compiled once, and each of its four first-class bindings (Python, C++, Go, Rust) calls that same core through this bridge.

**`.so` / `libaletheia-ffi.so`** — the compiled shared library that holds the verified core; every binding loads this one file at runtime, so they all run the exact same proven logic (the Windows and macOS equivalents would be `.dll` and `.dylib`).

---

## See Also

- **[Cookbook](guides/COOKBOOK.md)** — problem-driven recipes
- **[Quick Start](guides/QUICKSTART.md)** — 5-minute tutorial
- **[CLI Reference](reference/CLI.md)** — the `aletheia` command and its six subcommands
- **[Protocol Reference](architecture/PROTOCOL.md)** — the wire format and error codes
