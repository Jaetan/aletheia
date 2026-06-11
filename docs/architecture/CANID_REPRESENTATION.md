# CAN identifier representation — cross-binding rationale

Closes PY-S-20.1 (R21 Step 2 Python System).

The Aletheia stack's three language bindings represent a CAN
identifier — and the 11-bit-vs-29-bit `extended` discriminator —
slightly differently at the typed-API level.  The wire format is
identical across all three; the divergence is purely in the
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
| Python | `CANFrameTuple` | 7-NamedTuple `(timestamp, can_id: int, dlc, data, extended: bool, brs, esi)` | `validate_can_id(can_id, *, extended)` at `client/_types.py:430` |
| Go | `Frame` | 6-struct with `ID: CANID` (sealed interface — `StandardID(uint16) \| ExtendedID(uint32)`) | `NewStandardID(uint16) (StandardID, error)` / `NewExtendedID(uint32) (ExtendedID, error)` factory functions |
| C++ | `Frame` | 6-aggregate with `id: CanId` (`std::variant<StandardId, ExtendedId>` over private-ctor newtypes) | `StandardId::create(uint16_t)` / `ExtendedId::create(uint32_t)` factories returning `std::expected<…, std::string>` |

## Why Python is the outlier

The Go and C++ bindings encode the `extended` flag at the value level
via a discriminated union (`StandardID | ExtendedID` / `std::variant<>`),
giving compile-time guarantees that:

- `id.Value()` callers know whether the underlying integer is 11-bit
  or 29-bit without consulting a separate flag.
- Switch coverage is exhaustive (Go compiler / `std::visit`).
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
keyword-only kwarg.  Go and C++ encode this in the typed ID parameter
and have no such kwarg.  This asymmetry is a direct consequence of
the representation choice above — closing PY-S-20.1 would also close
PY-S-20.3 simultaneously, but only by accepting the Go/C++ ergonomic
cost on the Python side.

## When to re-evaluate

Promote `CanId = StandardId | ExtendedId` (path b in PY-S-20.1) if
either:

- The cross-binding documentation gap surfaces a real user-confusion
  signal (issue reports, mailing-list questions).
- A future Aletheia feature requires CAN-XL or remote-frame
  discrimination at the type level (where Python's tuple-of-primitives
  would force a `frame.kind: Literal["std", "ext", "remote", "xl"]`
  string discriminant — at that point the discriminated union becomes
  unambiguously better).

Until then the current shape is documented divergence, not drift.

## See also

- `docs/FEATURE_MATRIX.yaml` rows `canfd_brs_esi` / `mock_backend` /
  `backend_di_seam` for cross-binding feature parity tracking.
- `feedback_cross_binding_consistency_as_fp.md` for the project's
  convention on when cross-binding divergence is acceptable.
- `feedback_no_backward_compat.md` for the project's stance on
  breaking changes — the path-b promotion would be permitted but is
  not motivated today.
