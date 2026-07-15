-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Runtime decision procedure for `WellFormedTextDBCAgg`.
--
-- Emits one `ValidationIssue` per violated text-round-trip well-formedness
-- condition, so the `FormatDBCText` handler can report "round-trips, or here's at
-- least one reason it falls outside the proven round-trip envelope".
-- (`WellFormedTextDBCAgg` is SUFFICIENT-not-necessary for round-trip — a non-empty
-- result means "not proven to round-trip", never "will not".)  Runtime-side — NO
-- proofs; the soundness/completeness tree lives in
-- `Aletheia.DBC.TextParser.Properties.WellFormedCheck.Sound`.
--
-- All functions are cold-path (format path, not the per-frame streaming hot
-- path), so `Dec` allocation is acceptable here (the hot-path performance rule
-- applies to streaming only).
module Aletheia.DBC.TextParser.WellFormedCheck where

open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Bool.ListAction using (any; all)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; map; concatMap) renaming (_++_ to _++ₗ_)
open import Data.List.NonEmpty using () renaming (_∷_ to _∷⁺_)
open import Data.List.Relation.Unary.AllPairs using (allPairs?)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Maybe.Properties using (≡-dec)
open import Data.Nat using (ℕ; suc; _+_; _*_; _∸_)
open import Data.Nat.Properties using (_<?_; _≤?_; _≟_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String using (String; fromList) renaming (_++_ to _++ₛ_)
open import Relation.Nullary.Decidable using (¬?; ⌊_⌋)

open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.CAN.Constants using (max-physical-bits)
open import Aletheia.CAN.DLC using (dlcBytes)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian)
open import Aletheia.CAN.DBCHelpers using (_≟-CANId_)
open import Aletheia.DBC.Identifier using (Identifier; nameStr; _≟ᴵ_; _≡csᵇ_)
open import Aletheia.DBC.TextFormatter.Topology using (findMuxMaster)
open import Aletheia.DBC.TextFormatter.Attributes using (nthLabel; collectDefs)
open import Aletheia.DBC.TextParser.Attributes using (findLabel; lookupDef)
open import Aletheia.DBC.DecRat.Refinement using (natDecRatToℕ)
open import Aletheia.DBC.Types using
  ( RawValueDesc; ValidationIssue; mkIssue; IsWarning
  ; DBCSignal; DBCMessage; DBC; SignalPresence; Always; When
  ; AttrType; ATInt; ATFloat; ATString; ATEnum; ATHex
  ; AttrValue; AVInt; AVFloat; AVString; AVEnum; AVHex
  ; DuplicateSignalName; DuplicateMessageId; UnknownValueDescriptionTarget
  ; StartBitOutOfRange; BitLengthExcessive; BitLengthZero; SignalExceedsDLC
  ; BigEndianMSBLayout; MultiValueMuxSelector; MuxMasterIncoherent
  ; DBCAttribute; DBCAttrDef; DBCAttrDefault; DBCAttrAssign
  ; AttrDef; AttrDefault; AttrAssign
  ; AttributeEnumEmpty; UnknownAttributeName; AttributeValueTypeMismatch
  ; AttributeEnumDefaultUnstable )
open import Aletheia.DBC.Validity.Combinators using (requireDec)

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

-- ── signal arithmetic (WF `wf-sigs` = WellFormedSignalDef; `pvs` =
-- PhysicallyValid; `wfps` = single-value presence) ──────────────────────────
--
-- EXPOSED SCRUTINEE (feedback_expose_scrutinee_for_external_rewrite): `pvGo`
-- takes the `ByteOrder` and `pGo` the `SignalPresence` as explicit arguments and
-- pattern-match structurally — deliberately NO `with` here.  The checker is then
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

pGo : SignalPresence → String → List ValidationIssue
pGo Always                  _    = []
pGo (When _ (_ ∷⁺ []))      _    = []
pGo (When _ (_ ∷⁺ (_ ∷ _))) name =
  mkIssue IsWarning MultiValueMuxSelector
    ("signal '" ++ₛ name
     ++ₛ "': multi-value mux selector — text form emits only the first selector value")
  ∷ []

presenceIssue : DBCSignal → List ValidationIssue
presenceIssue s = pGo (DBCSignal.presence s) (nameStr (DBCSignal.name s))

-- ── master coherence (WF field `mc` = MasterCoherent), Bool leaves ──────────
--
-- Exposed on the `findMuxMaster` result: `mcGo` takes the `Maybe (List Char)`
-- master name as an argument, so the soundness proof (`mcGo-sound`) controls the
-- case-split externally.  Bool-valued,
-- no `with`.  `MasterCoherent` = single Always master, and every `When` selector
-- names it.

isAlwaysᵇ : SignalPresence → Bool
isAlwaysᵇ Always     = true
isAlwaysᵇ (When _ _) = false

masterOkᵇ : List Char → DBCSignal → Bool
masterOkᵇ n s = (Identifier.name (DBCSignal.name s) ≡csᵇ n) ∧ isAlwaysᵇ (DBCSignal.presence s)

wGo : List Char → SignalPresence → Bool
wGo _ Always     = true
wGo n (When m _) = Identifier.name m ≡csᵇ n

whenOkᵇ : List Char → DBCSignal → Bool
whenOkᵇ n s = wGo n (DBCSignal.presence s)

mcGo : Maybe (List Char) → List DBCSignal → Bool
mcGo nothing  _    = true
mcGo (just n) sigs = any (masterOkᵇ n) sigs ∧ all (whenOkᵇ n) sigs

masterCoherentᵇ : List DBCSignal → Bool
masterCoherentᵇ sigs = mcGo (findMuxMaster sigs) sigs

mcIssue : List DBCSignal → List ValidationIssue
mcIssue sigs =
  if masterCoherentᵇ sigs then []
  else mkIssue IsWarning MuxMasterIncoherent
         ("message multiplexing is incoherent (no single Always master, or a "
          ++ₛ "selector names a different master)")
       ∷ []

-- ── attributes (WF field `attr-wfs` = WFAttribute) — checked NOWHERE by the
-- validator today, so nothing to mirror; the leaves mirror the Properties
-- predicates directly.  (Chunk E1: the two structural Bool leaves.) ──────────

-- WfAttrType (Properties/Attributes/Def.agda): every AttrType is well-formed
-- EXCEPT an empty enum (`ATEnum []`), the sole reject.
wfAttrTypeIssues : AttrType → List ValidationIssue
wfAttrTypeIssues (ATEnum []) =
  mkIssue IsWarning AttributeEnumEmpty "attribute enum type declares no labels" ∷ []
wfAttrTypeIssues _ = []

-- ValueMatchesType (Properties/Attributes/Common.agda: VMTInt/Float/String/Enum/Hex
-- — the 5 diagonal constructor pairs).  `vmtᵇ` is its Bool image.
vmtᵇ : AttrType → AttrValue → Bool
vmtᵇ (ATInt _ _)   (AVInt _)    = true
vmtᵇ (ATFloat _ _) (AVFloat _)  = true
vmtᵇ ATString      (AVString _) = true
vmtᵇ (ATEnum _)    (AVEnum _)   = true
vmtᵇ (ATHex _ _)   (AVHex _)    = true
vmtᵇ _             _            = false

-- DefaultEnumOK (Properties/Aggregator/Foundations.agda:143-146): an ATEnum
-- default whose value is `AVEnum n` emits the label STRING `nthLabel n labels`,
-- which must resolve back to the SAME index — `findLabel (nthLabel n labels)
-- labels ≡ just n` (label uniqueness + index-in-bounds).  Vacuously `⊤` for every
-- non-(ATEnum × AVEnum) pair.  `enumOkᵇ` is its Bool image, decided by `Maybe ℕ`
-- decidable equality; the catch-all keeps it `with`-free (the soundness proof
-- re-matches these concrete patterns, where `DefaultEnumOK` reduces).  Only
-- the DEFAULT path consults it (assign values emit the index directly, no bridge).
enumOkᵇ : AttrType → AttrValue → Bool
enumOkᵇ (ATEnum labels) (AVEnum n) =
  ⌊ ≡-dec _≟_ (findLabel (nthLabel (natDecRatToℕ n) labels) labels)
              (just (natDecRatToℕ n)) ⌋
enumOkᵇ _ _ = true

-- ── attribute dispatch (WF field `attr-wfs` = WFAttribute, 3 arms) ───────────
--
-- `attrIssues` maps each `DBCAttribute` constructor to the matching `WFAttribute`
-- arm (Aggregator/Foundations.agda:148-160):
--   • `DBCAttrDef d`     → `wfDef`     : `WfAttrType (attrType d)`   (`wfAttrTypeIssues`)
--   • `DBCAttrDefault d` → `wfDefault` : name resolves + value matches + enum stable
--   • `DBCAttrAssign a`  → `wfAssign`  : name resolves + value matches (NO enum bridge)
--
-- EXPOSED SCRUTINEE (feedback_expose_scrutinee_for_external_rewrite): `attrIssues`
-- passes `lookupDef … : Maybe AttrDef` to `resolveDefIssues`/`enumDefaultIssue`,
-- which pattern-match it — so the soundness proof can `with (lookupDef …) in
-- eq` externally and both leaves reduce.  The `lookupDef` call is repeated (not
-- `let`-bound) on the default arm so the `with` abstracts both occurrences alike.

-- Name resolution + value/type match — the two premises SHARED by the default and
-- assign arms.  `nothing` (name never declared) → `UnknownAttributeName`; `just
-- def` → `AttributeValueTypeMismatch` unless `vmtᵇ` holds.
resolveDefIssues : Maybe AttrDef → AttrValue → String → List ValidationIssue
resolveDefIssues nothing    _ nm =
  mkIssue IsWarning UnknownAttributeName
    ("attribute '" ++ₛ nm ++ₛ "' is referenced but never declared (no BA_DEF_ line)") ∷ []
resolveDefIssues (just def) v _  =
  if vmtᵇ (AttrDef.attrType def) v then []
  else mkIssue IsWarning AttributeValueTypeMismatch
         "attribute value's constructor does not match the declared attribute type"
       ∷ []

-- Enum-default stability — the default-arm-ONLY premise (`DefaultEnumOK`).  Assign
-- values emit the index directly (`rawOfAssignValue`), so this is NOT consulted on
-- the assign arm.  `nothing` is already flagged by `resolveDefIssues`, so `[]` here.
enumDefaultIssue : Maybe AttrDef → AttrValue → List ValidationIssue
enumDefaultIssue nothing    _ = []
enumDefaultIssue (just def) v =
  if enumOkᵇ (AttrDef.attrType def) v then []
  else mkIssue IsWarning AttributeEnumDefaultUnstable
         "enum default label does not round-trip to its index (duplicate labels or out-of-range index)"
       ∷ []

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
-- `MessageWF` (Properties/Topology/Message.agda:559-578) bundles 9 fields; 4 are
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
-- Emits for exactly the 4 DECIDED Agg fields (WellFormed.agda:85-105); the other
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
