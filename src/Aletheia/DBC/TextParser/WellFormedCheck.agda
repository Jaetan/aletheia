-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Runtime decision procedure for `WellFormedTextDBCAgg`.
--
-- Emits one `ValidationIssue` per violated text-round-trip well-formedness
-- condition, so the `FormatDBCText` handler can report "round-trips, or here's at
-- least one reason it falls outside the proven round-trip envelope".
-- (`WellFormedTextDBCAgg` is SUFFICIENT-not-necessary for round-trip — a non-empty
-- result means "not proven to round-trip", never "will not".)  Runtime-side — no
-- standalone lemmas (`Dec`-valued leaves carry their own refutations); the
-- soundness/completeness tree lives in
-- `Aletheia.DBC.TextParser.Properties.WellFormedCheck.Sound`.
--
-- All functions are cold-path (format path, not the per-frame streaming hot
-- path), so `Dec` allocation is acceptable here (the hot-path performance rule
-- applies to streaming only).
--
-- ── TIGHTNESS: which conditions are round-trip-NECESSARY ─────────────────────
--
-- `WellFormedTextDBCAgg` is sufficient for the round-trip, but its fields are
-- not all necessary.  Some diagnostics below mark genuine loss — every
-- violating DBC fails `parseText ∘ formatText`, so the handler's per-DBC
-- `roundTripsWithᵇ` check (Protocol/Handlers/FormatDBCText.agda) refuses with
-- the typed `TextRoundTripFailed` error — while others mark only the boundary
-- of the proven envelope: violating DBCs exist that the kernel PROVES
-- round-trip (it emits their text, and emission is only reachable on a passed
-- check, per `formatDBCTextResult-sound`).  Each verdict below names the loss
-- (or loss-absence) mechanism and the witness class confirmed against the
-- running kernel with `format_dbc_text` as the exact oracle; "reachability"
-- says which public routes can put a violating DBC in front of the round-trip
-- check at all.
--
-- • `wf-sigs` (`checkSignalBounds` → StartBitOutOfRange / BitLengthExcessive):
--   UNREACHABLE — tight in principle, invariant by construction in practice.
--   The bounds are spent collapsing the text parser's entry clamps to
--   identities: `buildSignal` (TextParser/Topology/SignalLine.agda) reduces
--   the raw start bit and bit length modulo the physical-bit bounds, and
--   `bitLength-mod-id` / `unconvertSB-mod-id` (Properties/Topology/
--   Resolve.agda) consume the WF certificates to cancel those reductions.
--   But the SAME clamps run on every public parse route (`buildSignal` on
--   text, `parseSignalFields` in JSONParser.agda on the wire), so no
--   kernel-resident DBC can violate the bounds: out-of-range geometry is
--   normalized into range or refused with a typed parse error before a DBC
--   value exists.  Witness class: out-of-range start bits / lengths submitted
--   on every public parse route come back clamped in the kernel's own echo;
--   no diagnostic of this arm can fire on any publicly reachable DBC.
--
-- • `pvs` (`pvGo` → BitLengthZero / SignalExceedsDLC / BigEndianMSBLayout):
--   UNREACHABLE at the formatter — the gate deciding the condition also
--   guards the door.  The FormatDBCText handler re-parses its JSON `dbc`
--   argument through `parseDBCWithErrors`, whose `physicalGate` decides
--   exactly the `PhysicallyValid` conjuncts (machine-checked by
--   `parseSignalFields-pv`, JSONParser/SignalWF.agda) and refuses violators
--   with typed parse errors.  A DBC violating only the MSB-layout conjunct IS
--   kernel-reachable through the text route (it loads with warnings), but
--   that value cannot re-enter FormatDBCText.  In principle the conjuncts are
--   mixed: length-positivity is tight (a zero-length signal emits an SG_ line
--   `buildSignal` rejects on re-parse); the big-endian frame bound is tight
--   except on a monus-clamped fixed-point subclass no route constructs; the
--   MSB-layout hypothesis is bound but unused by
--   `unconvertStartBit-roundtrip` (CAN/Endianness/Properties/StartBit.agda) —
--   merely bundled for the format→parse direction.  Witness class: every
--   violating JSON submission is refused by `physicalGate` (typed
--   parse_signal_* errors), never by the round-trip check.
--
-- • `wfps` (`pGo` → MultiValueMuxSelector): TIGHT (round-trip-necessary);
--   reachable via the JSON routes.  `emitMuxMarker-chars`
--   (TextFormatter/Topology.agda) emits only the HEAD selector value, and —
--   stronger — `resolvePresence` (TextParser/Topology/SignalLine.agda) only
--   ever constructs singleton `When`, so a multi-value presence lies outside
--   the image of `parseText` altogether: no emitted text could round-trip it.
--   This is the counterexample class documented in
--   Properties/WellFormedFromValidity.agda.  Witness class: a multi-value
--   selector is refused (the divergence error plus this warning); the
--   singleton control succeeds.  The structural validator mirrors this
--   diagnostic warning-class (`checkAllMultiValueMuxSelectors` in
--   Validator/Checks.agda reuses `presenceIssue`), so `validateDBC` and the
--   loading routes also name the shape; warnings never block a load.
--
-- • `mc` (`mcIssue` → MuxMasterIncoherent): TIGHT; reachable via the JSON
--   routes.  A `When` slave's own master reference is dropped at emission
--   (`emitMuxMarker-chars` keeps only the selector value); the master's name
--   survives only as the `M` marker on an `Always` signal, and re-parse
--   rebinds every slave to that single `findMuxName` master
--   (`resolvePresence`).  Master absent → the marked block fails to re-parse;
--   a slave naming a different master → rebound to the emitted master, a
--   different DBC.  Witness class: absent-master, split-master, and
--   self-cycle DBCs are all refused; the split-master shape (slaves under two
--   `Always` masters) LOADS error-free — no error-class validator check
--   covers it, and the structural validator mirrors this diagnostic
--   warning-class (`checkAllMuxMasterIncoherent` in Validator/Checks.agda
--   reuses `mcIssue`), so the load surfaces the warning without blocking.
--   The text route cannot construct a violator (a parse either fails
--   or yields the single-master assignment, coherent by construction).
--
-- • `sig-names-unique` (`checkSigNamesUnique` → DuplicateSignalName):
--   MERELY-BUNDLED.  The proof spends it making the VAL_ re-attachment
--   collapse invariant: `formatText` flattens per-signal value descriptions
--   into VAL_ lines keyed (CAN id, signal name), and parse-back re-attaches
--   by `lookup-vd`'s FIRST match (TextParser/ValueDescriptions.agda), so
--   every same-named signal receives the group's first collected payload.
--   SG_ emission itself is positional and name-agnostic — name duplication
--   alone loses nothing.  Witness class: duplicate-name messages whose
--   same-named signals carry no (or identical) value descriptions FORMAT
--   SUCCESSFULLY with this warning attached — the emission is itself the
--   machine-checked round-trip proof — while divergent payloads under the
--   shared key are refused.  Load-unreachable: the validator's error-class
--   duplicate-signal-name check refuses every load route, so violators reach
--   the kernel only through the stateless FormatDBCText / ValidateDBC routes.
--
-- • `msg-ids-unique` (`checkMsgIdsUnique` → DuplicateMessageId):
--   MERELY-BUNDLED — the same first-match mechanism as `sig-names-unique`,
--   through the id-keyed collapse channels: VAL_ re-attachment keyed
--   (CAN id, signal name) (`lookup-vd`) and BO_TX_BU_ senders re-attachment
--   keyed on the CAN id alone (`lookup-senders`, TextParser/Senders.agda).
--   Witness class: duplicate-id DBCs with no (or identical) id-keyed payloads
--   format successfully with this warning; divergent VAL_ payloads or a
--   one-sided senders list are refused.  Load-unreachable (the validator's
--   duplicate-message-id check is error-class); note the same wire code is
--   warning-class here and error-class there.
--
-- • `attr-wfs` (`checkAttrs` → AttributeEnumEmpty / UnknownAttributeName /
--   AttributeValueTypeMismatch / AttributeEnumDefaultUnstable): TIGHT on
--   every arm; reachable via the JSON routes — including the LOAD route,
--   since the validator has no error-class attribute-shape checks.  Loss
--   sites: an empty-ENUM def emits a label list the grammar cannot re-parse
--   (`parseEnumLabels` demands at least one label); an undeclared name makes
--   `refineAttribute` fail on re-parse (and an enum default under a missing
--   def collapses to `emitDefaultValue-chars`' sentinel at emission);
--   off-diagonal values are re-typed by `refineDefaultValue` /
--   `refineAssignValue`, which dispatch on the DECLARED type, so re-parse can
--   only produce diagonal constructors; an unstable enum default emits its
--   label string and `findLabel`'s first match recovers a different index.
--   Witness class: every violating shape — including an integral float under
--   an INT def, and a string equal to a declared enum label — is refused with
--   exactly the matching warning riding the refusal; text-parsed DBCs satisfy
--   the field by construction (the text route cannot express a violator).
--
-- • `unresolved-empty` (`checkUnresolved` → UnknownValueDescriptionTarget):
--   TIGHT; reachable via the JSON and text routes alike (the JSON wire preserves a supplied
--   non-empty list verbatim, and the text route builds one from any stray
--   VAL_ line).  `formatChars` (TextFormatter/TopLevel.agda) has no operand
--   position for `DBC.unresolvedValueDescs` — the field has no emission site
--   (deliberately: see the field's comment in TextParser/WellFormed.agda) —
--   and parse-back rebuilds the field as `[]` unconditionally
--   (`unresolvedRVDs-on-clearBothMsgs-collectFromMessages`), so a non-empty
--   input diverges as a theorem-level falsity, not a coverage gap.  Witness
--   class: a stray unresolved entry via either route is refused with this
--   warning naming the offending entry; the empty control succeeds.
--
-- The verdicts are relative to the shipped emitter/parser pair: if
-- SG_MUL_VAL_ emission and cross-line resolution ever land (the extended-mux
-- design plan), `wfps` flips to merely-bundled on exactly the shapes that
-- syntax expresses, and nested multiplexing would force `MasterCoherent` —
-- and this classification — to be revisited.
module Aletheia.DBC.TextParser.WellFormedCheck where

open import Data.List using (List; []; _∷_; map; concatMap) renaming (_++_ to _++ₗ_)
open import Data.List.Relation.Unary.AllPairs using (allPairs?)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Maybe.Properties using (≡-dec)
open import Data.Nat using (ℕ; suc; _+_; _*_; _∸_)
open import Data.Nat.Properties using (_<?_; _≤?_; _≟_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String using (String; fromList) renaming (_++_ to _++ₛ_)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (Dec; yes; no; ¬?)

open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.CAN.Constants using (max-physical-bits)
open import Aletheia.CAN.DLC using (dlcBytes)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian)
open import Aletheia.CAN.DBCHelpers using (_≟-CANId_)
open import Aletheia.DBC.Identifier using (nameStr; _≟ᴵ_)
open import Aletheia.DBC.TextFormatter.Attributes using (nthLabel; collectDefs)
open import Aletheia.DBC.TextParser.Attributes using (findLabel; lookupDef)
open import Aletheia.DBC.TextParser.WellFormedAttr using
  ( ValueMatchesType; VMTInt; VMTFloat; VMTString; VMTEnum; VMTHex
  ; WfAttrType; WfATInt; WfATFloat; WfATString; WfATEnum; WfATHex
  ; DefaultEnumOK )
open import Aletheia.DBC.DecRat.Refinement using (natDecRatToℕ)
open import Aletheia.DBC.Types using
  ( RawValueDesc; ValidationIssue; mkIssue; IsWarning
  ; DBCSignal; DBCMessage; DBC
  ; AttrType; ATInt; ATFloat; ATString; ATEnum; ATHex
  ; AttrValue; AVInt; AVFloat; AVString; AVEnum; AVHex
  ; DuplicateSignalName; DuplicateMessageId; UnknownValueDescriptionTarget
  ; StartBitOutOfRange; BitLengthExcessive; BitLengthZero; SignalExceedsDLC
  ; BigEndianMSBLayout
  ; DBCAttribute; DBCAttrDef; DBCAttrDefault; DBCAttrAssign
  ; AttrDef; AttrDefault; AttrAssign
  ; AttributeEnumEmpty; UnknownAttributeName; AttributeValueTypeMismatch
  ; AttributeEnumDefaultUnstable )
open import Aletheia.DBC.Validity.Combinators using (requireDec)

-- The mux-presence (`wfps`) and master-coherence (`mc`) deciders live in the
-- Foundations submodule — the structural validator's warning-class mirrors
-- import them from there without dragging this module's text-parser closure.
-- Re-exported publicly so this module remains the single import surface for
-- the whole WF-checker family (wfTextIssues below composes them directly).
open import Aletheia.DBC.TextParser.WellFormedCheck.Foundations public

-- ── unresolved value descriptions (WF field `unresolved-empty`) ──────────────
--
-- One warning per entry of `DBC.unresolvedValueDescs`, reusing CHECK 23's code
-- (`UnknownValueDescriptionTarget`).  `formatText` emits no line for these, so
-- any non-empty entry is a round-trip loss.  Mirrors
-- `Validator/Checks.agda:checkUnknownValueDescriptionTarget` (same code, same
-- detail shape); re-derived here so the WF field is decided from THIS output.

showCanIdText : CANId → String
showCanIdText (CANId.Standard n _) = showℕ n
showCanIdText (CANId.Extended n _) = showℕ n

checkUnresolved : List RawValueDesc → List ValidationIssue
checkUnresolved = concatMap unresolvedIssue
  where
  unresolvedIssue : RawValueDesc → List ValidationIssue
  unresolvedIssue rvd =
    mkIssue IsWarning UnknownValueDescriptionTarget
      ("VAL_ entry: CAN ID " ++ₛ showCanIdText (RawValueDesc.canId rvd)
       ++ₛ ", signal '" ++ₛ nameStr (RawValueDesc.signalName rvd)
       ++ₛ "' not found (no message with this CAN ID has a signal with this name)")
    ∷ []

-- ── uniqueness (WF fields `sig-names-unique`, `msg-ids-unique`) ──────────────
--
-- Decide the record fields' EXACT mapped forms — `AllPairs _≢_ (map …)` — directly
-- with stdlib `allPairs?`, so `requireDec-sound` lands the field with no bridge
-- from the validator's string/list form.  `allPairs?` decides the whole
-- list, so the detail is generic (it does not single out the offending pair).

checkSigNamesUnique : List DBCSignal → List ValidationIssue
checkSigNamesUnique sigs =
  requireDec (allPairs? (λ i j → ¬? (i ≟ᴵ j)) (map DBCSignal.name sigs))
    (mkIssue IsWarning DuplicateSignalName
      "duplicate signal name within a message (text round-trip needs unique signal names)")

checkMsgIdsUnique : List DBCMessage → List ValidationIssue
checkMsgIdsUnique msgs =
  requireDec (allPairs? (λ x y → ¬? (x ≟-CANId y)) (map DBCMessage.id msgs))
    (mkIssue IsWarning DuplicateMessageId
      "duplicate message CAN ID (text round-trip needs unique message IDs)")

-- ── signal arithmetic (WF `wf-sigs` = All WellFormedSignal, whose payload is
-- WellFormedSignalDef — the two bounds decided here; `pvs` =
-- PhysicallyValid; the `wfps` single-value-presence decider lives in
-- Foundations, re-exported above) ────────────────────────────────────────────
--
-- EXPOSED SCRUTINEE: `pvGo`
-- takes the `ByteOrder` as an explicit argument and
-- pattern-matches structurally — deliberately NO `with` here.  The checker is then
-- a plain function of the scrutinee, so the soundness proof can
-- `with … in eq` the scrutinee EXTERNALLY and this application reduces cleanly
-- (past `with`-reduction failures came from `with`-abstracting internally).  Each
-- `requireDec` decides the EXACT proposition its WF record field carries
-- (Formatter/WellFormed.agda) so `requireDec-sound` lands it with no conversion.

checkSignalBounds : DBCSignal → List ValidationIssue
checkSignalBounds s =
  requireDec (SignalDef.startBit (DBCSignal.signalDef s) <? max-physical-bits)
    (mkIssue IsWarning StartBitOutOfRange
      ("signal '" ++ₛ nameStr (DBCSignal.name s) ++ₛ "': start bit ≥ the physical-bit bound"))
  ++ₗ
  requireDec (SignalDef.bitLength (DBCSignal.signalDef s) <? suc max-physical-bits)
    (mkIssue IsWarning BitLengthExcessive
      ("signal '" ++ₛ nameStr (DBCSignal.name s) ++ₛ "': bit length exceeds the physical-bit bound"))

pvGo : ByteOrder → ℕ → SignalDef → String → List ValidationIssue
pvGo LittleEndian _ sd name =
  requireDec (1 ≤? SignalDef.bitLength sd)
    (mkIssue IsWarning BitLengthZero
      ("signal '" ++ₛ name ++ₛ "': bit length must be at least 1"))
pvGo BigEndian fb sd name =
  requireDec (1 ≤? SignalDef.bitLength sd)
    (mkIssue IsWarning BitLengthZero
      ("signal '" ++ₛ name ++ₛ "': bit length must be at least 1"))
  ++ₗ
  requireDec (SignalDef.startBit sd + SignalDef.bitLength sd ∸ 1 <? fb * 8)
    (mkIssue IsWarning SignalExceedsDLC
      ("signal '" ++ₛ name ++ₛ "': big-endian signal exceeds the frame bit width"))
  ++ₗ
  requireDec (SignalDef.bitLength sd ∸ 1 ≤? SignalDef.startBit sd)
    (mkIssue IsWarning BigEndianMSBLayout
      ("signal '" ++ₛ name ++ₛ "': big-endian MSB layout (bitLength − 1 must be ≤ startBit)"))

pvIssues : ℕ → DBCSignal → List ValidationIssue
pvIssues fb s = pvGo (DBCSignal.byteOrder s) fb (DBCSignal.signalDef s) (nameStr (DBCSignal.name s))

-- ── attributes (WF field `attr-wfs` = WFAttribute) — checked NOWHERE by the
-- validator today, so nothing to mirror; the leaves decide the shared
-- `WellFormedAttr` predicates directly with stock `Dec`. ─────────────────────

-- WfAttrType: every AttrType is well-formed EXCEPT an empty enum
-- (`ATEnum []`), the sole reject (its `WfATEnum` constructor demands a cons).
wfAttrType? : (t : AttrType) → Dec (WfAttrType t)
wfAttrType? (ATInt mn mx)     = yes (WfATInt mn mx)
wfAttrType? (ATFloat mn mx)   = yes (WfATFloat mn mx)
wfAttrType? ATString          = yes WfATString
wfAttrType? (ATEnum [])       = no λ ()
wfAttrType? (ATEnum (x ∷ xs)) = yes (WfATEnum x xs)
wfAttrType? (ATHex mn mx)     = yes (WfATHex mn mx)

wfAttrTypeIssues : AttrType → List ValidationIssue
wfAttrTypeIssues t =
  requireDec (wfAttrType? t)
    (mkIssue IsWarning AttributeEnumEmpty "attribute enum type declares no labels")

-- ValueMatchesType has exactly the 5 diagonal `AT*`↔`AV*` constructor pairs,
-- so the decider is the 5×5 double-match: each diagonal clause returns the
-- constructor (carrying the value witness); the 20 off-diagonal pairs have no
-- constructor, so `no λ ()` refutes.
vmt? : (t : AttrType) (v : AttrValue) → Dec (ValueMatchesType t v)
vmt? (ATInt _ _)   (AVInt z)    = yes (VMTInt z)
vmt? (ATFloat _ _) (AVFloat d)  = yes (VMTFloat d)
vmt? ATString      (AVString s) = yes (VMTString s)
vmt? (ATEnum _)    (AVEnum n)   = yes (VMTEnum n)
vmt? (ATHex _ _)   (AVHex n)    = yes (VMTHex n)
vmt? (ATInt _ _)   (AVFloat _)  = no λ ()
vmt? (ATInt _ _)   (AVString _) = no λ ()
vmt? (ATInt _ _)   (AVEnum _)   = no λ ()
vmt? (ATInt _ _)   (AVHex _)    = no λ ()
vmt? (ATFloat _ _) (AVInt _)    = no λ ()
vmt? (ATFloat _ _) (AVString _) = no λ ()
vmt? (ATFloat _ _) (AVEnum _)   = no λ ()
vmt? (ATFloat _ _) (AVHex _)    = no λ ()
vmt? ATString      (AVInt _)    = no λ ()
vmt? ATString      (AVFloat _)  = no λ ()
vmt? ATString      (AVEnum _)   = no λ ()
vmt? ATString      (AVHex _)    = no λ ()
vmt? (ATEnum _)    (AVInt _)    = no λ ()
vmt? (ATEnum _)    (AVFloat _)  = no λ ()
vmt? (ATEnum _)    (AVString _) = no λ ()
vmt? (ATEnum _)    (AVHex _)    = no λ ()
vmt? (ATHex _ _)   (AVInt _)    = no λ ()
vmt? (ATHex _ _)   (AVFloat _)  = no λ ()
vmt? (ATHex _ _)   (AVString _) = no λ ()
vmt? (ATHex _ _)   (AVEnum _)   = no λ ()

-- DefaultEnumOK is the bridge `findLabel (nthLabel n labels) labels ≡ just n`
-- on exactly (ATEnum, AVEnum) — where the decider IS `Maybe ℕ` decidable
-- equality — and `⊤` (so `yes tt`) everywhere else.  Match the AttrType
-- FIRST, mirroring `DefaultEnumOK`'s own clause order, so every clause's
-- goal reduces (under a non-enum type it is `⊤` for ANY value).  Only the
-- DEFAULT path consults it (assign values emit the index directly, no bridge).
enumOk? : (t : AttrType) (v : AttrValue) → Dec (DefaultEnumOK t v)
enumOk? (ATEnum labels) (AVEnum n) =
  ≡-dec _≟_ (findLabel (nthLabel (natDecRatToℕ n) labels) labels)
            (just (natDecRatToℕ n))
enumOk? (ATInt _ _)   _            = yes tt
enumOk? (ATFloat _ _) _            = yes tt
enumOk? ATString      _            = yes tt
enumOk? (ATHex _ _)   _            = yes tt
enumOk? (ATEnum _)    (AVInt _)    = yes tt
enumOk? (ATEnum _)    (AVFloat _)  = yes tt
enumOk? (ATEnum _)    (AVString _) = yes tt
enumOk? (ATEnum _)    (AVHex _)    = yes tt

-- ── attribute dispatch (WF field `attr-wfs` = WFAttribute, 3 arms) ───────────
--
-- `attrIssues` maps each `DBCAttribute` constructor to the matching `WFAttribute`
-- arm (Aggregator/Foundations.agda, `WFAttribute`):
--   • `DBCAttrDef d`     → `wfDef`     : `WfAttrType (attrType d)`   (`wfAttrTypeIssues`)
--   • `DBCAttrDefault d` → `wfDefault` : name resolves + value matches + enum stable
--   • `DBCAttrAssign a`  → `wfAssign`  : name resolves + value matches (NO enum bridge)
--
-- EXPOSED SCRUTINEE: `attrIssues`
-- passes `lookupDef … : Maybe AttrDef` to `resolveDefIssues`/`enumDefaultIssue`,
-- which pattern-match it — so the soundness proof can `with (lookupDef …) in
-- eq` externally and both leaves reduce.  The `lookupDef` call is repeated (not
-- `let`-bound) on the default arm so the `with` abstracts both occurrences alike.

-- Name resolution + value/type match — the two premises SHARED by the default and
-- assign arms.  `nothing` (name never declared) → `UnknownAttributeName`; `just
-- def` → `AttributeValueTypeMismatch` unless `ValueMatchesType` holds.
resolveDefIssues : Maybe AttrDef → AttrValue → String → List ValidationIssue
resolveDefIssues nothing    _ nm =
  mkIssue IsWarning UnknownAttributeName
    ("attribute '" ++ₛ nm ++ₛ "' is referenced but never declared (no BA_DEF_ line)") ∷ []
resolveDefIssues (just def) v _  =
  requireDec (vmt? (AttrDef.attrType def) v)
    (mkIssue IsWarning AttributeValueTypeMismatch
      "attribute value's constructor does not match the declared attribute type")

-- Enum-default stability — the default-arm-ONLY premise (`DefaultEnumOK`).  Assign
-- values emit the index directly (`rawOfAssignValue`), so this is NOT consulted on
-- the assign arm.  `nothing` is already flagged by `resolveDefIssues`, so `[]` here.
enumDefaultIssue : Maybe AttrDef → AttrValue → List ValidationIssue
enumDefaultIssue nothing    _ = []
enumDefaultIssue (just def) v =
  requireDec (enumOk? (AttrDef.attrType def) v)
    (mkIssue IsWarning AttributeEnumDefaultUnstable
      "enum default label does not round-trip to its index (duplicate labels or out-of-range index)")

attrIssues : List AttrDef → DBCAttribute → List ValidationIssue
attrIssues _    (DBCAttrDef d)     = wfAttrTypeIssues (AttrDef.attrType d)
attrIssues defs (DBCAttrDefault d) =
     resolveDefIssues (lookupDef (AttrDefault.name d) defs) (AttrDefault.value d)
                      (fromList (AttrDefault.name d))
  ++ₗ enumDefaultIssue (lookupDef (AttrDefault.name d) defs) (AttrDefault.value d)
attrIssues defs (DBCAttrAssign a)  =
  resolveDefIssues (lookupDef (AttrAssign.name a) defs) (AttrAssign.value a)
                   (fromList (AttrAssign.name a))

checkAttrs : List DBCAttribute → List ValidationIssue
checkAttrs attrs = concatMap (attrIssues (collectDefs attrs)) attrs

-- ── per-message aggregate (WF field `msg-wfs` = MessageWF) ───────────────────
--
-- `MessageWF` (Properties/Topology/Message.agda) bundles 9 fields; 4 are
-- FREE: `fb-bound` (vacuous — `dlcBytes … ≤ 64` always), `name-pre`/`send-pre`
-- (identNameStop), `item-pres` (the universal `recvHeadStop`).
-- `checkTextMessage` decides the remaining 5:
--   • wf-sigs          → per-signal `checkSignalBounds`
--   • pvs              → per-signal `pvIssues (dlcBytes (dlc m))`  (frame-byte width)
--   • wfps             → per-signal `presenceIssue`
--   • mc               → `mcIssue (signals m)`
--   • sig-names-unique → `checkSigNamesUnique (signals m)`
checkTextMessage : DBCMessage → List ValidationIssue
checkTextMessage m =
     checkSigNamesUnique (DBCMessage.signals m)
  ++ₗ mcIssue            (DBCMessage.signals m)
  ++ₗ concatMap checkSignalBounds                        (DBCMessage.signals m)
  ++ₗ concatMap (pvIssues (dlcBytes (DBCMessage.dlc m))) (DBCMessage.signals m)
  ++ₗ concatMap presenceIssue                            (DBCMessage.signals m)

-- ── top-level checker: the runtime image of `WellFormedTextDBCAgg` ───────────
--
-- Emits for exactly the 4 DECIDED `WellFormedTextDBCAgg` fields
-- (TextParser/WellFormed.agda); the other
-- 5 (`node-stops`, `vt-stops`, `ev-stops`, `cm-stops`, `sg-wfs`) are name-stop
-- predicates discharged unconditionally by `wellFormedFromValidity`, so no
-- line here.
--   • msg-wfs          → `concatMap checkTextMessage (messages d)`
--   • msg-ids-unique   → `checkMsgIdsUnique (messages d)`
--   • attr-wfs         → `checkAttrs (attributes d)`   (`collectDefs` applied inside)
--   • unresolved-empty → `checkUnresolved (unresolvedValueDescs d)`
wfTextIssues : DBC → List ValidationIssue
wfTextIssues d =
     concatMap checkTextMessage (DBC.messages d)
  ++ₗ checkMsgIdsUnique          (DBC.messages d)
  ++ₗ checkAttrs                 (DBC.attributes d)
  ++ₗ checkUnresolved            (DBC.unresolvedValueDescs d)
