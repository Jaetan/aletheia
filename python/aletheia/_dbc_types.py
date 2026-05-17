"""DBC structure TypedDicts (private — re-exported via ``aletheia.protocols``).

Holds the cross-binding DBC wire schema: the leaf type aliases
(:data:`ByteOrder`, :data:`SignalPresence`, :data:`DLCByteCount`,
:data:`DLCCode`) plus every ``DBC*`` TypedDict.  Split out of
``protocols.py`` (R19 cluster 17 follow-up, 2026-05-12) once the latter
crossed the 1000-line pylint C0302 threshold; ``aletheia.protocols``
remains the canonical public surface via re-export.
"""

from fractions import Fraction
from typing import Literal, NewType, NotRequired, TypedDict


ByteOrder = Literal["little_endian", "big_endian"]

SignalPresence = Literal["always", "multiplexed"]


# R19 cluster 17 / PY-D-19.4: distinguish DLC byte count from DLC code at
# the type level.  Both wrap ``int`` at runtime; JSON wire shape unchanged.
# Go's ``aletheia.DLC`` + C++'s ``aletheia::DLC`` are the cross-binding
# equivalents.  ``dlc_to_bytes`` / ``bytes_to_dlc`` mediate between them.
DLCByteCount = NewType("DLCByteCount", int)  # bytes, {0..8, 12, 16, 20, 24, 32, 48, 64}
DLCCode = NewType("DLCCode", int)            # 4-bit wire field, 0..15


class DBCSignalAlways(TypedDict):
    """DBC signal that is always present.

    Numeric fields (factor/offset/minimum/maximum) use ``Fraction`` to
    preserve the Agda core's exact rational representation end-to-end.
    ``receivers`` is the trailing node list from the ``SG_`` line
    (empty list when only the ``Vector__XXX`` placeholder is present).
    ``valueDescriptions`` carries the inline ``VAL_`` entries attached to
    this signal (empty list when no ``VAL_`` line names it).
    """
    name: str
    startBit: int
    length: int
    byteOrder: ByteOrder
    signed: bool
    factor: Fraction
    offset: Fraction
    minimum: Fraction
    maximum: Fraction
    unit: str
    presence: SignalPresence
    receivers: NotRequired[list[str]]
    valueDescriptions: NotRequired[list["DBCValueEntry"]]


class DBCSignalMultiplexed(TypedDict):
    """DBC signal that is conditionally present (multiplexed).

    Numeric fields (factor/offset/minimum/maximum) use ``Fraction`` to
    preserve the Agda core's exact rational representation end-to-end.
    ``receivers`` is the trailing node list from the ``SG_`` line
    (empty list when only the ``Vector__XXX`` placeholder is present).
    ``valueDescriptions`` carries the inline ``VAL_`` entries attached to
    this signal (empty list when no ``VAL_`` line names it).

    The ``presence`` field is narrowed to ``Literal["multiplexed"]`` so
    consumers can use it as the discriminator when pattern-matching against
    the ``DBCSignal`` union.  :class:`DBCSignalAlways` keeps the wider
    :data:`SignalPresence` type and so does not narrow on construction.
    """
    name: str
    startBit: int
    length: int
    byteOrder: ByteOrder
    signed: bool
    factor: Fraction
    offset: Fraction
    minimum: Fraction
    maximum: Fraction
    unit: str
    presence: Literal["multiplexed"]
    multiplexor: str
    multiplex_values: list[int]
    receivers: NotRequired[list[str]]
    valueDescriptions: NotRequired[list["DBCValueEntry"]]


# Union type for all signal types
DBCSignal = DBCSignalAlways | DBCSignalMultiplexed


class DBCMessage(TypedDict):
    """DBC message definition structure.

    Note: ``dlc`` is the payload byte count (from ``cantools message.length``),
    typed as :data:`DLCByteCount` rather than ``int`` to keep it
    distinguishable from :data:`DLCCode` (the 4-bit wire field on a CAN
    frame).  For CAN 2.0B (DLC 0-8) the byte count and DLC code coincide;
    for CAN-FD (DLC 9-15) this field holds 12/16/20/24/32/48/64 bytes.
    The JSON key name ``"dlc"`` matches the Agda parser's wire format
    (the NewType is type-level only — runtime is plain ``int``).
    """
    id: int
    name: str
    dlc: DLCByteCount
    sender: str
    senders: NotRequired[list[str]]  # Additional BO_TX_BU_ transmitters (primary is ``sender``)
    signals: list[DBCSignal]
    extended: NotRequired[bool]  # Optional: true for 29-bit, false/absent for 11-bit


class DBCSignalGroup(TypedDict):
    """DBC signal group (``SIG_GROUP_`` keyword).

    The DBC spec carries a parent-message id and a repetition count on the
    wire; the Agda core only models the flattened ``{name, signals}`` view
    because signal-name uniqueness is enforced globally by the validator,
    so reconstructing message context on format_dbc is unnecessary.
    """
    name: str
    signals: list[str]


# DBC environment variable type (``EV_`` ``type`` field).
# The DBC spec encodes int/float/string as 0/1/2 respectively; the Agda
# core preserves that wire vocabulary directly (``varTypeToℕ``).
DBCVarType = Literal[0, 1, 2]


class DBCEnvironmentVar(TypedDict):
    """DBC environment variable (``EV_`` keyword).

    Numeric fields (initial/minimum/maximum) use ``Fraction`` for the same
    reason as ``DBCSignalAlways`` — the Agda core works in ℚ and exact
    rational precision has to survive the wire round-trip.
    """
    name: str
    varType: DBCVarType
    initial: Fraction
    minimum: Fraction
    maximum: Fraction


class DBCValueEntry(TypedDict):
    """One entry in a DBC value table (numeric value → description)."""
    value: int
    description: str


class DBCValueTable(TypedDict):
    """DBC value table (``VAL_TABLE_`` keyword)."""
    name: str
    entries: list[DBCValueEntry]


# ----------------------------------------------------------------------------
# Tier 2 DBC metadata: nodes / comments / attributes
# ----------------------------------------------------------------------------
# Every tagged wire object (CommentTarget, AttrType, AttrValue, AttrTarget,
# DBCAttribute) uses ``"kind"`` as the first-field discriminator. This mirrors
# the Agda formatter exactly (see ``Formatter.agda`` ``formatCommentTarget`` /
# ``formatAttribute``), so pyright narrows via ``Literal["kind"]``.

class DBCNode(TypedDict):
    """DBC network node (``BU_`` keyword). Only the declared name is modelled;
    per-node attributes and comments live in the sibling arrays."""
    name: str


class DBCCommentTargetNetwork(TypedDict):
    """Network-wide comment (``CM_ "..."``)."""
    kind: Literal["network"]


class DBCCommentTargetNode(TypedDict):
    """Node comment (``CM_ BU_ <name> "..."``)."""
    kind: Literal["node"]
    node: str


class DBCCommentTargetMessage(TypedDict):
    """Message comment (``CM_ BO_ <id> "..."``).

    ``extended`` follows the same convention as ``DBCMessage``: ``true`` for
    29-bit IDs, absent/``false`` for 11-bit IDs.
    """
    kind: Literal["message"]
    id: int
    extended: NotRequired[bool]


class DBCCommentTargetSignal(TypedDict):
    """Signal comment (``CM_ SG_ <id> <signal> "..."``)."""
    kind: Literal["signal"]
    id: int
    extended: NotRequired[bool]
    signal: str


class DBCCommentTargetEnvVar(TypedDict):
    """Environment-variable comment (``CM_ EV_ <name> "..."``)."""
    kind: Literal["envVar"]
    envVar: str


DBCCommentTarget = (
    DBCCommentTargetNetwork |
    DBCCommentTargetNode |
    DBCCommentTargetMessage |
    DBCCommentTargetSignal |
    DBCCommentTargetEnvVar
)


class DBCComment(TypedDict):
    """A DBC ``CM_`` entry with its target and body."""
    target: DBCCommentTarget
    text: str


# Attribute scope matches Agda ``AttrScope``. ``nodeMsg`` / ``nodeSig`` are
# the relational scopes introduced by ``BA_DEF_REL_`` (``BU_BO_REL_`` /
# ``BU_SG_REL_`` in DBC text).
AttrScope = Literal[
    "network", "node", "message", "signal", "envVar", "nodeMsg", "nodeSig"
]


class DBCAttrTypeInt(TypedDict):
    """Integer attribute definition (``INT min max``).

    ``min`` / ``max`` are encoded as JSON numbers and carry the full ℤ range
    of the Agda core — handlers that marshal them should use unbounded
    integers, not fixed-width.
    """
    kind: Literal["int"]
    min: int
    max: int


class DBCAttrTypeFloat(TypedDict):
    """Float attribute definition (``FLOAT min max``).

    Bounds are ``Fraction`` to preserve ℚ precision across the wire;
    cantools emits ``float`` literals which the converter widens to
    ``Fraction`` for lossless round-trip.
    """
    kind: Literal["float"]
    min: Fraction
    max: Fraction


class DBCAttrTypeString(TypedDict):
    """String attribute definition (``STRING``)."""
    kind: Literal["string"]


class DBCAttrTypeEnum(TypedDict):
    """Enum attribute definition (``ENUM "a","b",...``)."""
    kind: Literal["enum"]
    values: list[str]


class DBCAttrTypeHex(TypedDict):
    """Hex attribute definition (``HEX min max``). Bounds are unsigned ℕ."""
    kind: Literal["hex"]
    min: int
    max: int


DBCAttrType = (
    DBCAttrTypeInt |
    DBCAttrTypeFloat |
    DBCAttrTypeString |
    DBCAttrTypeEnum |
    DBCAttrTypeHex
)


class DBCAttrValueInt(TypedDict):
    """Integer attribute value (BA_/BA_DEF_DEF_/BA_REL_ for ``INT``)."""
    kind: Literal["int"]
    value: int


class DBCAttrValueFloat(TypedDict):
    """Float attribute value (``FLOAT``). ``Fraction`` mirrors
    ``DBCAttrTypeFloat.min`` / ``max``."""
    kind: Literal["float"]
    value: Fraction


class DBCAttrValueString(TypedDict):
    """String attribute value."""
    kind: Literal["string"]
    value: str


class DBCAttrValueEnum(TypedDict):
    """Enum attribute value: ``value`` is a 0-based index into the matching
    definition's ``values`` list (ℕ on the Agda side), not the label."""
    kind: Literal["enum"]
    value: int


class DBCAttrValueHex(TypedDict):
    """Hex attribute value (unsigned ℕ)."""
    kind: Literal["hex"]
    value: int


DBCAttrValue = (
    DBCAttrValueInt |
    DBCAttrValueFloat |
    DBCAttrValueString |
    DBCAttrValueEnum |
    DBCAttrValueHex
)


class DBCAttrTargetNetwork(TypedDict):
    """Network-scope attribute assignment (``BA_ "attr" value;``)."""
    kind: Literal["network"]


class DBCAttrTargetNode(TypedDict):
    """Node-scope assignment (``BA_ "attr" BU_ <node> value;``)."""
    kind: Literal["node"]
    node: str


class DBCAttrTargetMessage(TypedDict):
    """Message-scope assignment (``BA_ "attr" BO_ <id> value;``)."""
    kind: Literal["message"]
    id: int
    extended: NotRequired[bool]


class DBCAttrTargetSignal(TypedDict):
    """Signal-scope assignment (``BA_ "attr" SG_ <id> <sig> value;``)."""
    kind: Literal["signal"]
    id: int
    extended: NotRequired[bool]
    signal: str


class DBCAttrTargetEnvVar(TypedDict):
    """EnvVar-scope assignment (``BA_ "attr" EV_ <name> value;``)."""
    kind: Literal["envVar"]
    envVar: str


class DBCAttrTargetNodeMsg(TypedDict):
    """Node-message relational assignment (``BA_REL_ ... BU_BO_REL_ ...``)."""
    kind: Literal["nodeMsg"]
    node: str
    id: int
    extended: NotRequired[bool]


class DBCAttrTargetNodeSig(TypedDict):
    """Node-signal relational assignment (``BA_REL_ ... BU_SG_REL_ ...``)."""
    kind: Literal["nodeSig"]
    node: str
    id: int
    extended: NotRequired[bool]
    signal: str


DBCAttrTarget = (
    DBCAttrTargetNetwork |
    DBCAttrTargetNode |
    DBCAttrTargetMessage |
    DBCAttrTargetSignal |
    DBCAttrTargetEnvVar |
    DBCAttrTargetNodeMsg |
    DBCAttrTargetNodeSig
)


class DBCAttrDef(TypedDict):
    """Attribute declaration (``BA_DEF_`` / ``BA_DEF_REL_``)."""
    kind: Literal["definition"]
    name: str
    scope: AttrScope
    attrType: DBCAttrType


class DBCAttrDefault(TypedDict):
    """Attribute default (``BA_DEF_DEF_`` / ``BA_DEF_DEF_REL_``)."""
    kind: Literal["default"]
    name: str
    value: DBCAttrValue


class DBCAttrAssign(TypedDict):
    """Attribute assignment (``BA_`` / ``BA_REL_``)."""
    kind: Literal["assignment"]
    name: str
    target: DBCAttrTarget
    value: DBCAttrValue


# The three BA_* sub-records live in a single flat list so wire ordering
# (definition → default → assignment) is preserved end-to-end; the ``kind``
# discriminator lets the Agda parser dispatch without separate arrays.
DBCAttribute = DBCAttrDef | DBCAttrDefault | DBCAttrAssign


class DBCRawValueDesc(TypedDict):
    """Unresolved ``VAL_`` line from the DBC text-parse path.

    Carries the owning message's CAN ID, the signal name, and the
    ``(value, label)`` entries.  Populated only when the text-parse path
    encounters a ``VAL_`` line whose ``(canId, signalName)`` pair does
    not match any signal in the parsed messages; the entries are
    preserved verbatim so the validator's CHECK 23
    ``UnknownValueDescriptionTarget`` can warn at validation time.
    """
    id: int
    extended: NotRequired[bool]
    signalName: str
    entries: list["DBCValueEntry"]


class DBCDefinition(TypedDict):
    """Complete DBC file structure.

    R19 cluster 17 / PY-D-19.6 (2026-05-12): every metadata array is
    REQUIRED to match Go/C++ struct shape (where fields are non-optional
    by language idiom).  Use ``[]`` for sections the file has no entries
    for; hand-written fixtures must enumerate all keys.
    """
    version: str
    messages: list[DBCMessage]
    signalGroups: list[DBCSignalGroup]
    environmentVars: list[DBCEnvironmentVar]
    valueTables: list[DBCValueTable]
    nodes: list[DBCNode]
    comments: list[DBCComment]
    attributes: list[DBCAttribute]
    unresolvedValueDescs: list[DBCRawValueDesc]


class _DBCTier2Empty(TypedDict):
    """Helper TypedDict carrying the 7 Tier-2 fields of :class:`DBCDefinition`.

    Returned by :func:`empty_dbc_tier2`; spread with ``**`` into a
    ``DBCDefinition`` literal that supplies only ``version`` and
    ``messages``.  Exists to dedupe the ``[]``-default boilerplate that
    every hand-written fixture or normalisation site otherwise repeats
    verbatim (pylint R0801 follow-up to PY-D-19.6 closure).
    """
    signalGroups: list[DBCSignalGroup]
    environmentVars: list[DBCEnvironmentVar]
    valueTables: list[DBCValueTable]
    nodes: list[DBCNode]
    comments: list[DBCComment]
    attributes: list[DBCAttribute]
    unresolvedValueDescs: list[DBCRawValueDesc]


def empty_dbc_tier2() -> _DBCTier2Empty:
    """Return ``[]`` defaults for the 7 :class:`DBCDefinition` Tier-2 fields.

    Use as ``{"version": v, "messages": ms, **empty_dbc_tier2()}`` when
    constructing a :class:`DBCDefinition` without metadata.  Each call
    returns a fresh dict; the inner lists are never shared between
    callers, so mutations stay local.
    """
    return {
        "signalGroups": [],
        "environmentVars": [],
        "valueTables": [],
        "nodes": [],
        "comments": [],
        "attributes": [],
        "unresolvedValueDescs": [],
    }
