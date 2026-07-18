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
module Aletheia.DBC.TextParser.WellFormedCheck where

open import Data.Char using (Char) renaming (_≟_ to _≟ᶜ_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; map; concatMap) renaming (_++_ to _++ₗ_)
open import Data.List.Membership.Propositional using (find; lose)
open import Data.List.NonEmpty using (List⁺) renaming (_∷_ to _∷⁺_)
import Data.List.Properties as ListProps
open import Data.List.Relation.Unary.All as All using (all?)
open import Data.List.Relation.Unary.AllPairs using (allPairs?)
open import Data.List.Relation.Unary.Any using (any?)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Maybe.Properties using (≡-dec; just-injective)
open import Data.Nat using (ℕ; suc; _+_; _*_; _∸_)
open import Data.Nat.Properties using (_<?_; _≤?_; _≟_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; fromList) renaming (_++_ to _++ₛ_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Relation.Nullary.Decidable using (Dec; yes; no; ¬?; _×-dec_)

open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.CAN.Constants using (max-physical-bits)
open import Aletheia.CAN.DLC using (dlcBytes)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian)
open import Aletheia.CAN.DBCHelpers using (_≟-CANId_)
open import Aletheia.DBC.Identifier using (Identifier; nameStr; _≟ᴵ_)
open import Aletheia.DBC.Formatter.WellFormedText.Foundations using (MasterCoherent; mc-no-mux; mc-mux)
open import Aletheia.DBC.TextFormatter.Topology using (findMuxMaster)
open import Aletheia.DBC.TextFormatter.Attributes using (nthLabel; collectDefs)
open import Aletheia.DBC.TextParser.Attributes using (findLabel; lookupDef)
open import Aletheia.DBC.TextParser.WellFormedAttr using
  ( ValueMatchesType; VMTInt; VMTFloat; VMTString; VMTEnum; VMTHex
  ; WfAttrType; WfATInt; WfATFloat; WfATString; WfATEnum; WfATHex
  ; DefaultEnumOK )
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

-- ── signal arithmetic (WF `wf-sigs` = All WellFormedSignal, whose payload is
-- WellFormedSignalDef — the two bounds decided here; `pvs` =
-- PhysicallyValid; `wfps` = single-value presence) ──────────────────────────
--
-- EXPOSED SCRUTINEE: `pvGo`
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

-- ── master coherence (WF field `mc` = MasterCoherent), decided directly ─────
--
-- `MasterCoherent` (Formatter/WellFormedText/Foundations.agda) = single `Always` master, and
-- every `When` selector names it.  Decided by stock `Dec`: `any? (masterOk? n)`
-- exhibits the master (with the `∈` witness `mc-mux` needs, via `find`) and
-- `all? (whenOk? n)` lands the slaves `All` field verbatim, so `requireDec-sound`
-- turns "no issue" into the WF field with no Bool-reflection bridge.  `mcGo?`
-- takes the `findMuxMaster` result as an argument together with its equation
-- (`masterCoherent?` instantiates `refl`), keeping the case-split `with`-free
-- on the scrutinee.

isAlways? : (p : SignalPresence) → Dec (p ≡ Always)
isAlways? Always     = yes refl
isAlways? (When _ _) = no λ ()

-- The master conjunct of `mc-mux`: the signal carries the master's name and is
-- `Always`-present — exactly the constructor's name/presence witness pair.
MasterOk : List Char → DBCSignal → Set
MasterOk n s = (Identifier.name (DBCSignal.name s) ≡ n) × (DBCSignal.presence s ≡ Always)

masterOk? : (n : List Char) (s : DBCSignal) → Dec (MasterOk n s)
masterOk? n s =
  ListProps.≡-dec _≟ᶜ_ (Identifier.name (DBCSignal.name s)) n
    ×-dec isAlways? (DBCSignal.presence s)

-- The slave conjunct of `mc-mux`, stated in the SAME ∀-shape as the
-- constructor's `All` field, so `all? (whenOk? n) sigs` produces that field
-- with no per-element conversion.
WhenNames : List Char → SignalPresence → Set
WhenNames n p = ∀ (m : Identifier) (vs : List⁺ ℕ) → p ≡ When m vs → Identifier.name m ≡ n

whenNames? : (n : List Char) (p : SignalPresence) → Dec (WhenNames n p)
whenNames? n Always      = yes λ _ _ ()
whenNames? n (When m vs) with ListProps.≡-dec _≟ᶜ_ (Identifier.name m) n
... | yes eq = yes λ { _ _ refl → eq }
... | no ¬eq = no λ f → ¬eq (f m vs refl)

whenOk? : (n : List Char) (s : DBCSignal) → Dec (WhenNames n (DBCSignal.presence s))
whenOk? n s = whenNames? n (DBCSignal.presence s)

private
  just≢nothing : ∀ {A : Set} {x : A} → just x ≡ nothing → ⊥
  just≢nothing ()

mcGo? : (mm : Maybe (List Char)) (sigs : List DBCSignal)
  → findMuxMaster sigs ≡ mm → Dec (MasterCoherent sigs)
mcGo? nothing  sigs eq = yes (mc-no-mux eq)
mcGo? (just n) sigs eq
  with any? (masterOk? n) sigs ×-dec all? (whenOk? n) sigs
... | yes (anyOk , allOk) =
  let (ms , ms∈sigs , nameEq , presEq) = find anyOk
  in yes (mc-mux n eq ms ms∈sigs nameEq presEq allOk)
... | no ¬both = no λ where
  (mc-no-mux eqN) → just≢nothing (trans (sym eq) eqN)
  (mc-mux n′ eq′ ms ms∈sigs nameEq presEq slaves) →
    let n′≡n = just-injective (trans (sym eq′) eq)
    in ¬both ( lose ms∈sigs (trans nameEq n′≡n , presEq)
             , All.map (λ {s} f m vs weq → trans (f m vs weq) n′≡n) slaves )

masterCoherent? : (sigs : List DBCSignal) → Dec (MasterCoherent sigs)
masterCoherent? sigs = mcGo? (findMuxMaster sigs) sigs refl

mcIssue : List DBCSignal → List ValidationIssue
mcIssue sigs =
  requireDec (masterCoherent? sigs)
    (mkIssue IsWarning MuxMasterIncoherent
      ("message multiplexing is incoherent (no single Always master, or a "
       ++ₛ "selector names a different master)"))

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
