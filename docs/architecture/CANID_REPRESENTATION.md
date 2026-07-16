# CAN identifier representation — cross-binding rationale

The Aletheia stack's four language bindings represent a CAN
identifier — and the 11-bit-vs-29-bit `extended` discriminator —
slightly differently at the typed-API level.  The wire format is
identical across all four; the divergence is purely in the
binding-internal types that surface to user code.

## Wire format (identical)

- Numeric ID: `uint32` in JSON; passed as a `uint32` scalar argument to the
  binary FFI `aletheia_send_frame` (not a serialized little-endian field).
- Extended-frame flag: `uint8` (0 or 1) alongside the ID.

This shape is fixed by the Agda kernel's `CANId` ADT
(`src/Aletheia/CAN/Frame.agda`) and the FFI marshalling in
`haskell-shim/src/AletheiaFFI.hs`.

## Binding-level types

| Binding | API type | Shape | Validation site |
|---|---|---|---|
| Python | `CANFrameTuple` | 7-NamedTuple `(timestamp, can_id: int, dlc, data, extended: bool, brs, esi)` | `validate_can_id(can_id, *, extended)` in `python/aletheia/client/_types.py` |
| Go | `Frame` | 6-struct with `ID: CANID` (sealed interface — `StandardID(uint16) \| ExtendedID(uint32)`) | `NewStandardID(uint16) (StandardID, error)` / `NewExtendedID(uint32) (ExtendedID, error)` factory functions |
| C++ | `Frame` | 6-aggregate with `id: CanId` (`std::variant<StandardId, ExtendedId>` over private-ctor newtypes) | `StandardId::create(uint16_t)` / `ExtendedId::create(uint32_t)` factories returning `std::expected<…, std::string>` |
| Rust | `Frame` | struct with `id: CanId` (sealed enum — `Standard(u16) \| Extended(u32)`) | `CanId::standard(u16)` / `CanId::extended(u32)` factories returning `Result<…, Error>` |

## Why Python is the outlier

The Go, C++, and Rust bindings encode the `extended` flag at the value level
via a discriminated union (`StandardID | ExtendedID` / `std::variant<>` / a
native `enum`), giving compile-time guarantees that:

- `id.Value()` callers know whether the underlying integer is 11-bit
  or 29-bit without consulting a separate flag.
- Switch coverage is exhaustive (Go compiler / `std::visit` / Rust `match`).
- The "you forgot to pass `extended`" footgun cannot occur — the
  type-system requires choosing a constructor.

Python intentionally favours a `(can_id: int, extended: bool)` pair
because:

1. **Structural typing cost.**  Promoting `CanId = StandardId |
   ExtendedId` would require either two `NewType` wrappers (heavier
   than `int` at every callsite) or a small ADT — both introduce
   surface that the Python audience (data scientists, automotive
   engineers writing one-off scripts) finds less ergonomic than
   `client.send_frame(ts, 0x100, 8, data)`.
2. **`isinstance` checks vs `extended` flag.**  Python users routinely
   read `frame.extended` from `iter_can_log()` output to filter ID
   ranges; replacing that with `isinstance(frame.id, ExtendedID)` is
   strictly equivalent but adds a vocabulary item without easing the
   common path.
3. **`Optional[bool]` interop with `python-can`.**  Upstream
   `python-can` records arbitration-ID extended-frame flag as a bool;
   matching the Python type-shape preserves zero-conversion interop
   on the `iter_can_log` boundary.

## Consequence: Python's `extended=` kwarg

The Python `AletheiaClient.send_frame(ts, can_id, dlc, data, *,
extended=False, brs=None, esi=None)` carries an explicit `extended=`
keyword-only kwarg.  Go, C++, and Rust encode this in the typed ID parameter
and have no such kwarg.  This asymmetry is a direct consequence of
the representation choice above — closing this gap would also remove the
`extended=` kwarg asymmetry simultaneously, but only by accepting the
Go/C++/Rust ergonomic cost on the Python side.

## When to re-evaluate

Promote `CanId = StandardId | ExtendedId` (the discriminated-union
path) if either:

- The cross-binding documentation gap surfaces a real user-confusion
  signal (issue reports, mailing-list questions).
- A future Aletheia feature requires CAN-XL or remote-frame
  discrimination at the type level (where Python's tuple-of-primitives
  would force a `frame.kind: Literal["std", "ext", "remote", "xl"]`
  string discriminant — at that point the discriminated union becomes
  unambiguously better).

Until then the current shape is documented divergence, not drift.

## See also

- `docs/FEATURE_MATRIX.yaml` rows `canfd_brs_esi_fields` / `mock_backend` /
  `backend_di_seam` for cross-binding feature parity tracking.
- On when cross-binding divergence is acceptable: consistency across bindings is
  a goal, but not at the cost of each language's idioms — a divergence is not
  automatically a defect.
- On breaking changes: the project keeps no backward-compatibility guarantee, so
  the path-b promotion would be permitted, but it is not motivated today.
