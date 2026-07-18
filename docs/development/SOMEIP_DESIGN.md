# SOME/IP Support — Design Draft

---
**Status**: Draft — proposed design, not scheduled, no implementation started
**Last Updated**: 2026-07-18
**Scope**: A verified SOME/IP *monitor* (offline pcap / passive tap), not a transport stack
---

This document proposes how Aletheia grows from a CAN/CAN-FD verifier into a
two-protocol verifier with SOME/IP (Scalable service-Oriented MiddlewarE over IP,
the AUTOSAR service middleware for automotive Ethernet) as a peer protocol. It
records the architecture decisions and their rationale so implementation can
start from a settled design.

## 1. Motivation and product scope

SOME/IP traffic is service-oriented RPC (requests, responses, notifications,
service discovery) over UDP/TCP — structurally different from CAN's broadcast
frames, but the *verification questions* are the same shape: temporal properties
over a timestamped event stream ("every request is answered within 50 ms",
"session IDs increase monotonically per client", "a subscription is renewed
before its TTL expires").

**The niche Aletheia targets is empty.** Interactive bench tools (Vector CANoe
with the Ethernet option) own simulation and scripted testing but offer no
formal guarantees; open-source implementations (COVESA vsomeip) are transport
*stacks*, not analyzers; no formally verified SOME/IP decoder or monitor exists.
Aletheia's differentiator — machine-checked decoding and LTL evaluation — lands
intact in this niche without competing with either incumbent.

**In scope**: decoding SOME/IP messages from captured or tapped traffic
(pcap-derived byte streams delivered through the existing FFI), typed payload
deserialization driven by a verified service catalog, LTL property evaluation
over the resulting event stream, and SOME/IP-SD (service discovery) monitoring.

**Out of scope** (deferred, revisit on consumer demand): implementing a SOME/IP
endpoint or any transport; SOME/IP-TP segment reassembly; TCP stream
reassembly; E2E protection profiles; live network capture inside Aletheia
itself (the host application feeds bytes, as it already does for CAN frames).

## 2. Decision summary

| Question | Decision |
|---|---|
| Artifact | **One `libaletheia-ffi.so`** grows an `aletheia_someip_*` export family — no second shared library |
| Kernel | The LTL kernel is **parameterized in place** over its observation type; CAN and SOME/IP become peer instantiations |
| Kernel purity | Enforced by a **build gate** (kernel modules must import neither `Aletheia.CAN.*` nor `Aletheia.SomeIP.*`), with an injected-violation test proving the gate can fail |
| Service description | A small **verified JSON service catalog** parsed in Agda + **per-binding unverified `arxml2sid` converters** (one per language, packaged like the Excel loaders), XSD-assisted where the language has a mature validator, all converging on the verified catalog validator |
| Delivery | Six slices, each independently shippable; slice 1 is a zero-behavior-change refactor that ships with all four bindings green |

## 3. Why one shared library, not two

A dedicated `libaletheia-someip.so` was evaluated and rejected. The analysis
matters because parts of it are counter-intuitive:

**The GHC runtime is not the obstacle.** The foreign library does not embed the
RTS; it dynamically links `libHSrts*.so` (shipped beside the library,
`RPATH=$ORIGIN`). Two Haskell foreign libraries built on the **same GHC pin**
would reference the identical RTS soname, the dynamic loader deduplicates it,
and `hs_init` is multi-call tolerant — one process, one RTS, safely. Two
*distinct* RTS instances arise only under mixed GHC pins or a static RTS, which
GHC does not support in one process (signal-handler and `GHCRTS` clashes).

**The obstacle is a benefit vacuum.** Because both libraries would need the
same verified kernel, a split produces two thin shims over one full-size shared
core: no smaller artifact for CAN-only consumers, no memory saving, no fault
isolation (one RTS, shared CAF state). Meanwhile the split would re-plumb the
entire shipped distribution chain — `shake dist`'s single-artifact
chain-of-custody hashing, MANIFEST, SBOM, signing, `install.sh`, the loaders in
all four bindings — and create failure modes that do not exist today (two
libraries hand-copied from different releases silently coexisting with
divergent kernels).

**Escape hatch, recorded but deferred**: if a second artifact is ever genuinely
needed, the clean route is a Cabal internal `library aletheia-kernel` with two
thin `foreign-library` stanzas. Under the same-GHC-pin invariant this still
yields one RTS. Nothing in the proposed design forecloses it.

## 4. Kernel parameterization

The LTL kernel's coupling to CAN is nominal, not structural — which is why
parameterization is cheap:

- The formula AST is already generic: `LTL (Atom : Set)` in
  `Aletheia.LTL.Syntax`, with `mapLTL` as its functor map.
- The evaluation kernel (`Aletheia.LTL.Coalgebra.stepL`, denotational
  `Aletheia.LTL.Semantics.⟦_⟧`) names `TimedFrame`, but the **only** operation
  it performs on the event is reading its timestamp (inside the metric
  operators). Atom evaluation flows entirely through the opaque table
  `PredTable = ℕ → event → TruthVal`.
- The adequacy theorem (`Aletheia.LTL.Adequacy`) is universally quantified over
  that table, so it ports to a generalized event type by parameterization —
  **not** by restatement. The same holds for the incremental-evaluation and
  simplification soundness families.
- The only kernel type that stores a whole event is `Counterexample`
  (`Aletheia.LTL.Incremental`); its downstream consumers read only the
  timestamp.

**Design**: the kernel module family (`Coalgebra`, `Semantics`, `Adequacy`,
`Incremental`, and their property modules) gains a module-level parameter — the
observation type plus a timestamp projection. `TimedFrame` instantiates it for
CAN; a new `SomeIpEvent` (timestamp + header fields + payload bytes)
instantiates it for SOME/IP. Files stay where they are: protocol-agnosticism is
enforced by the import gate, not by moving modules, which keeps the refactor
diff reviewable and the proof bodies intact.

**The atom seam**: a protocol plugs into properties by providing one function
of shape `name → config → payload → Maybe ℚ` (CAN's is signal extraction
grounded in the DBC; SOME/IP's is field extraction grounded in the service
catalog). The last-known-value cache, the three-valued `TruthVal` logic, and
every proof above the predicate table are shared as-is.

**Hot-path constraint**: parameterization must compile to direct calls, not
runtime dictionary passing, on the per-message path — the same Bool-fast-path
discipline the CAN hot path follows (see `extractSignalCoreFast`). Module
parameters (which MAlonzo specializes at instantiation) are the default; any
alternative encoding must benchmark neutral on the existing CAN throughput
suite before it lands.

## 5. The SOME/IP protocol surface

Modeled in a new `Aletheia.SomeIP.*` package (peer of `Aletheia.CAN.*`):

- **Header** (16 bytes): Message ID (Service ID × Method/Event ID), Length,
  Request ID (Client ID × Session ID), protocol version, interface version,
  message type (REQUEST / REQUEST_NO_RETURN / NOTIFICATION / RESPONSE / ERROR),
  return code — as validated newtypes, mirroring the CAN ID / DLC treatment.
- **Events**: a timestamped event record and event ADT covering the message
  types, feeding the parameterized kernel exactly as CAN's trace events do.
- **Payload deserialization**: a verified reader for the SOME/IP serialization
  universe, staged — v1 covers fixed-width scalars and structs (with optional
  length fields and skip-extra semantics), fixed and dynamic arrays, and
  length-prefixed strings; the TLV / optional-member mode ("SOME/IP TLV") and
  unions come later. Termination follows the existing discipline: structural
  recursion on input length (`Aletheia.Parser.Combinators` is precedent; an
  exact-length byte reader is the natural substrate).
- **Service discovery**: SOME/IP-SD messages are ordinary SOME/IP payloads with
  a fixed entry/option layout (16-byte entries, option-index cross-references).
  SD gives the richest temporal-property material: offer/find/subscribe state
  machines, TTL expiry and renewal, reboot detection.

## 6. Service catalog: the DBC analogue

SOME/IP payload decoding needs a service interface description — the analogue
of the DBC file. The industry format is AUTOSAR ARXML: a very large XML schema
of which service interfaces are a small slice.

**Decision: do not build a verified ARXML parser.** The economics are decisive:
the verified `.dbc` *text* layer — for a flat, line-oriented format vastly
simpler than ARXML — accounts for roughly two-thirds of the Agda modules in the
repository (`cabal run shake -- count-modules` for current numbers). Repeating
that for ARXML would dwarf the rest of the SOME/IP program combined.

Instead:

1. **A small Aletheia-native JSON service catalog** — services, their
   methods/events/fields, and each one's typed parameter signature — parsed and
   validated in Agda on the existing JSON infrastructure, with
   soundness/completeness theorems for the validator (the pattern the DBC
   validator already follows).
2. **Per-binding unverified `arxml2sid` converters** (outside the trusted
   computing base) that extract the catalog from ARXML — one per language, so
   every consumer can go from an ARXML delivery to a checkable catalog without
   leaving their ecosystem. Packaging follows the Excel-loader precedent:
   an optional Python extra (`aletheia[arxml]`, lxml-backed), a separate Go
   module beside `go/excel/` (stdlib `encoding/xml`), a separate Rust crate
   beside `rust/excel/` (`quick-xml`/`roxmltree`), and a C++ component behind a
   CMake option (libxml2). Each CLI grows an `arxml2sid` subcommand.

**Keeping four converters honest.** Independent converters can drift; three
mechanisms hold them together, strongest last:

- **XML-schema validation of the input, where the ecosystem supports it.**
  ARXML is XML with official per-release AUTOSAR XSD schemas (declared by the
  file's `xsi:schemaLocation`), so schema validation catches malformed or
  truncated deliveries early with precise diagnostics. Mature XSD validators
  exist for Python (lxml) and C++ (libxml2); Go and Rust lack one, so those
  converters validate well-formedness plus the structural expectations of the
  service-interface slice they read. The XSD is therefore a diagnostics and
  input-hardening layer, not the trust anchor — no converter's correctness may
  depend on schema validation having run.
- **A shared ARXML fixture corpus with canonical catalog snapshots** — the
  DBC-corpus-parity pattern: every converter must produce byte-identical
  canonical catalogs from the shared fixtures, and the corpus grows a fixture
  with every converter bug found in any one language.
- **The verified catalog validator as the single arbiter.** Whatever a
  converter emits is vetted by the Agda validator for internal coherence
  (duplicate identifiers, signature well-formedness, reference integrity)
  before the kernel consumes it. Wrong converter output produces a *rejected
  catalog*, not silent misdecoding; the trust boundary stays exactly here.

## 7. Slice plan

Each slice ships independently, gates green, before the next starts:

1. **Kernel generalization (CAN-only ship).** Parameterize the kernel family;
   move the byte/fixed-width readers to a shared `Aletheia.Data.*` home; add the
   kernel-purity gate with its injected-violation test. Zero behavior change;
   all four bindings green with zero edits. This slice de-risks everything after
   it.
2. **Tracer bullet.** Header-only SOME/IP property check end-to-end in one
   binding (Python): UDP, no TP, fixed-width scalars; a real property such as
   per-client session-ID monotonicity evaluated over a pcap-derived stream.
3. **Service catalog + payload decode v1.** The JSON catalog, validator
   theorems, struct/array/string deserialization, typed field predicates; the
   first `arxml2sid` converter (Python, lxml + XSD validation) together with
   the shared ARXML fixture corpus and canonical catalog snapshots.
4. **Four-binding parity.** `SomeIpClient` siblings in Go/C++/Rust, backend
   seams and mocks, feature-matrix rows, log events; the remaining three
   `arxml2sid` converters, snapshot-tested against the shared corpus, plus the
   `arxml2sid` CLI subcommand in each CLI.
5. **SD monitoring.** Entry/option decoding; offer/subscribe/TTL state machines
   exposed as LTL-checkable events.
6. **Session correlation + TLV.** Request→response pairing (bounded state with
   typed overflow errors) and the TLV serialization mode.

Rough scale, reasoned against the existing per-package module counts: on the
order of 60–100 new Agda modules across all six slices; the tracer bullet
(slices 1–2) is roughly a third of that.

## 8. Design cautions

- **Do not reuse `DBC.Identifier` for service/method names.** Its character
  class and decidable-equality lemma chain are load-bearing for DBC parsing;
  dotted service paths need their own name type, designed in slice 1.
- **Never fork the adequacy theorem per protocol.** If parameterization of a
  proof family turns out harder than expected, the answer is more
  parameterization work — not a per-protocol copy of the kernel proofs.
- **UDP capture reordering is an ingestion concern.** The metric-temporal
  proofs assume monotone timestamps (`Monotonic` in `Aletheia.Trace`); the
  SOME/IP ingestion layer must sort or reject out-of-order input rather than
  weakening the theorems.

## 9. References

- AUTOSAR PRS — SOME/IP Protocol Specification
  (<https://www.autosar.org/fileadmin/standards/R24-11/FO/AUTOSAR_FO_PRS_SOMEIPProtocol.pdf>)
- AUTOSAR PRS — SOME/IP Service Discovery Protocol Specification
  (<https://www.autosar.org/fileadmin/standards/R24-11/FO/AUTOSAR_FO_PRS_SOMEIPServiceDiscoveryProtocol.pdf>)
- COVESA vsomeip (<https://github.com/COVESA/vsomeip>) — the reference
  open-source stack (transport + SD; no payload typing, no verification)
- Wireshark SOME/IP dissector — practical evidence that offline pcap analysis
  is the established workflow this design plugs into
