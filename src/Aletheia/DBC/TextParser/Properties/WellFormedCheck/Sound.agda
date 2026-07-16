-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Facade for the E.2 route (b) checker soundness/completeness tree: assembles the
-- signal/master/attribute leaf lemmas (`Sound.Signal`/`.Master`/`.Attr`) into the
-- per-message `MessageWF` reconstruction and the top theorem
-- `wfTextIssues d ≡ [] ⟺ WellFormedTextDBCAgg d`, composing through
-- `wellFormedFromValidity` (which discharges the five name-stop Agg fields).
-- The proof-tree ROOT for slice 1 (added to `proofModules` at S1.6 wiring).
--
-- Built in sub-chunks, each type-checked standalone:
--   S1.6a  issue-list → predicate bridges (mcIssue / sig-names / msg-ids / unresolved)  (this file, first)
--   S1.6b  `checkTextMessage-sound` (the full MessageWF record) + `signalLineWF-of`
--   S1.6c  `wfTextIssues-sound`   (top, via wellFormedFromValidity)
--   S1.6d  the completeness duals
module Aletheia.DBC.TextParser.Properties.WellFormedCheck.Sound where

open import Data.List using (List; []; _∷_; map)
open import Data.Bool.Properties using (T-≡)
open import Data.Product using (proj₁; proj₂)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary.Decidable using (¬?)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; allPairs?)
import Data.List.Relation.Unary.All as All
open All using (All)

open import Aletheia.CAN.DLC using (dlcBytes)
open import Aletheia.CAN.DBCHelpers using (_≟-CANId_)
open import Aletheia.DBC.Identifier using (_≟ᴵ_)
open import Aletheia.DBC.Types using (DBC; DBCSignal; DBCMessage; DBCAttribute; RawValueDesc)
open import Aletheia.DBC.Formatter.WellFormedText using (MasterCoherent; WellFormedTextPresence)
open import Aletheia.DBC.Validity.Combinators using (requireDec-sound; requireDec-complete)
open import Aletheia.DBC.Validity.ListLemmas using
  (++-≡[]-split; ++-≡[]-combine; concatMap-≡[]-sound; concatMap-≡[]-complete)
open import Aletheia.DBC.JSONParser.MessageWF using (dlcBytes-bounded)
open import Aletheia.DBC.TextFormatter.Attributes using (collectDefs)
open import Aletheia.DBC.TextParser.WellFormed using (WellFormedTextDBCAgg)
open import Aletheia.DBC.TextParser.Properties.Aggregator.Foundations using (WFAttribute)
open import Aletheia.DBC.TextParser.WellFormedCheck using
  (mcIssue; masterCoherentᵇ; checkSigNamesUnique; checkMsgIdsUnique; checkUnresolved; checkTextMessage; checkAttrs; wfTextIssues)
open import Aletheia.DBC.TextParser.Properties.Topology.Message using (MessageWF)
open import Aletheia.DBC.TextParser.Properties.Topology.SignalList using (SignalLineWF)
open import Aletheia.DBC.TextParser.Properties.Topology.Signal using (recvHeadStop)
open import Aletheia.DBC.TextParser.Properties.WellFormedFromValidity using
  (identNameStop; signalNameStop; wellFormedFromValidity)
open import Aletheia.DBC.TextParser.Properties.WellFormedCheck.Sound.Master using
  (masterCoherentᵇ-sound; masterCoherentᵇ-complete)
open import Aletheia.DBC.TextParser.Properties.WellFormedCheck.Sound.Signal using
  (signalBounds-sound; pGo-sound; pvGo-sound;
   signalBounds-complete; pGo-complete; pvGo-complete)
open import Aletheia.DBC.TextParser.Properties.WellFormedCheck.Sound.Attr using
  (if-[]-sound; attrIssues-sound; if-[]-complete; attrIssues-complete)

-- ── issue-list → predicate bridges (soundness) ───────────────────────────────
--
-- The per-message/per-DBC checker parts each emit a single issue kind; these
-- flat named lemmas turn "that part ≡ []" into the matching WF predicate,
-- internalising the `if`-elim / `requireDec-sound` / empty-list reasoning so the
-- `MessageWF` / `WellFormedTextDBCAgg` assembly (S1.6b/c) reads as a flat record.

-- `mcIssue sigs = if masterCoherentᵇ sigs then [] else (…∷[])`; peel the `if`
-- (`if-[]-sound`, reused from Sound.Attr), turn `T b` into `b ≡ true` (`T-≡`),
-- feed `masterCoherentᵇ-sound`.
mcIssue-sound : ∀ (sigs : List DBCSignal) → mcIssue sigs ≡ [] → MasterCoherent sigs
mcIssue-sound sigs eq =
  masterCoherentᵇ-sound sigs (Equivalence.to T-≡ (if-[]-sound (masterCoherentᵇ sigs) _ eq))

-- Both uniqueness parts decide `AllPairs _≢_ (map … )` directly (the checker's
-- `allPairs? (¬? ∘ _≟_)` is exactly `Dec (AllPairs _≢_ …)`), so `requireDec-sound`
-- lands them — pass the `Dec` explicitly (requireDec explicit-dec discipline).
checkSigNamesUnique-sound : ∀ (sigs : List DBCSignal)
  → checkSigNamesUnique sigs ≡ [] → AllPairs _≢_ (map DBCSignal.name sigs)
checkSigNamesUnique-sound sigs eq =
  requireDec-sound (allPairs? (λ i j → ¬? (i ≟ᴵ j)) (map DBCSignal.name sigs)) _ eq

checkMsgIdsUnique-sound : ∀ (msgs : List DBCMessage)
  → checkMsgIdsUnique msgs ≡ [] → AllPairs _≢_ (map DBCMessage.id msgs)
checkMsgIdsUnique-sound msgs eq =
  requireDec-sound (allPairs? (λ x y → ¬? (x ≟-CANId y)) (map DBCMessage.id msgs)) _ eq

-- `checkUnresolved` emits one non-empty issue PER entry, so `≡ []` forces the
-- list empty: `[]` gives `refl`, a cons makes the head issue `≢ []` (`()`).
checkUnresolved-sound : ∀ (rvds : List RawValueDesc) → checkUnresolved rvds ≡ [] → rvds ≡ []
checkUnresolved-sound []       _  = refl
checkUnresolved-sound (_ ∷ _)  ()

-- ── per-message reconstruction: checkTextMessage m ≡ [] → MessageWF m (S1.6b) ─

-- One `SignalLineWF` per signal: the presence witness comes from the shared
-- `wfps` (never re-derived), the name-stop / receiver-head-stop from the
-- always-total helpers `signalNameStop` / `recvHeadStop`.
signalLineWF-of : ∀ (s : DBCSignal)
  → WellFormedTextPresence (DBCSignal.presence s) → SignalLineWF s
signalLineWF-of s wp = record
  { name-stop      = signalNameStop s
  ; recv-head-stop = recvHeadStop (DBCSignal.receivers s)
  ; presence-wf    = wp
  }

-- `checkTextMessage m` is the 5-part `++ₗ` chain (WellFormedCheck.agda:290);
-- split it left-to-right into the five decided parts, then rebuild each
-- `MessageWF` field.  The four free fields (`fb-bound`, both name-pres,
-- `item-pres`) come from always-total helpers; `item-pres` reads the
-- where-bound `wfps-all`, NOT the sibling `wfps` field.
checkTextMessage-sound : ∀ (m : DBCMessage) → checkTextMessage m ≡ [] → MessageWF m
checkTextMessage-sound m premise = record
  { fb-bound         = dlcBytes-bounded (DBCMessage.dlc m)
  ; wf-sigs          = All.map (λ {s} → signalBounds-sound s) (concatMap-≡[]-sound c-eq)
  ; pvs              = All.map
      (λ {s} p → pvGo-sound (DBCSignal.byteOrder s) fb (DBCSignal.signalDef s) _ s refl refl p)
      (concatMap-≡[]-sound d-eq)
  ; wfps             = wfps-all
  ; mc               = mcIssue-sound sigs b-eq
  ; name-pre         = identNameStop (DBCMessage.name m)
  ; send-pre         = identNameStop (DBCMessage.sender m)
  ; item-pres        = All.map (λ {s} → signalLineWF-of s) wfps-all
  ; sig-names-unique = checkSigNamesUnique-sound sigs a-eq
  }
  where
    sigs = DBCMessage.signals m
    fb   = dlcBytes (DBCMessage.dlc m)
    -- split1..4 name the intermediate tails so the projections stay flat
    -- (named lemmas over nested proj₁/proj₂, per the abstraction discipline).
    split1 = ++-≡[]-split premise
    a-eq   = proj₁ split1                                  -- checkSigNamesUnique sigs ≡ []
    split2 = ++-≡[]-split (proj₂ split1)
    b-eq   = proj₁ split2                                  -- mcIssue sigs ≡ []
    split3 = ++-≡[]-split (proj₂ split2)
    c-eq   = proj₁ split3                                  -- concatMap checkSignalBounds sigs ≡ []
    split4 = ++-≡[]-split (proj₂ split3)
    d-eq   = proj₁ split4                                  -- concatMap (pvIssues fb) sigs ≡ []
    e-eq   = proj₂ split4                                  -- concatMap presenceIssue sigs ≡ []
    wfps-all = All.map (λ {s} p → pGo-sound (DBCSignal.presence s) _ p)
                 (concatMap-≡[]-sound e-eq)

-- ── the top theorem: wfTextIssues d ≡ [] → WellFormedTextDBCAgg d (S1.6c) ─────

-- `checkAttrs attrs = concatMap (attrIssues (collectDefs attrs)) attrs`; every
-- attribute is checked against the SAME `collectDefs attrs`, so the per-attr
-- soundness maps straight through.
checkAttrs-sound : ∀ (attrs : List DBCAttribute)
  → checkAttrs attrs ≡ [] → All (WFAttribute (collectDefs attrs)) attrs
checkAttrs-sound attrs eq =
  All.map (λ {a} → attrIssues-sound (collectDefs attrs) a) (concatMap-≡[]-sound eq)

-- `wfTextIssues d` is the 4-part `++ₗ` chain (WellFormedCheck.agda:308) emitting
-- for exactly the 4 DECIDED Agg fields; split it, rebuild those four, and hand
-- them to `wellFormedFromValidity`, which discharges the 5 free name-stop fields.
wfTextIssues-sound : ∀ (d : DBC) → wfTextIssues d ≡ [] → WellFormedTextDBCAgg d
wfTextIssues-sound d premise =
  wellFormedFromValidity d
    (All.map (λ {m} → checkTextMessage-sound m) (concatMap-≡[]-sound p-eq))  -- All MessageWF
    (checkAttrs-sound     (DBC.attributes d)          r-eq)                  -- All WFAttribute
    (checkMsgIdsUnique-sound (DBC.messages d)         q-eq)                  -- AllPairs _≢_ ids
    (checkUnresolved-sound (DBC.unresolvedValueDescs d) s-eq)               -- unresolved ≡ []
  where
    split1 = ++-≡[]-split premise
    p-eq   = proj₁ split1                    -- concatMap checkTextMessage (messages d) ≡ []
    split2 = ++-≡[]-split (proj₂ split1)
    q-eq   = proj₁ split2                    -- checkMsgIdsUnique (messages d) ≡ []
    split3 = ++-≡[]-split (proj₂ split2)
    r-eq   = proj₁ split3                    -- checkAttrs (attributes d) ≡ []
    s-eq   = proj₂ split3                    -- checkUnresolved (unresolvedValueDescs d) ≡ []

-- ── completeness: the well-formed side emits no issues (S1.6d) ────────────────
--
-- The exact duals of the sound bridges: each `-complete` leaf turns the matching
-- WF predicate back into "that checker part ≡ []", and the fixed `++ₗ` chains are
-- reassembled with `++-≡[]-combine` (one node per `++ₗ`, mirroring the structure —
-- not an equational tower).  Together with the sound direction this makes
-- `wfTextIssues` a genuine decision procedure for `WellFormedTextDBCAgg`.

mcIssue-complete : ∀ (sigs : List DBCSignal) → MasterCoherent sigs → mcIssue sigs ≡ []
mcIssue-complete sigs mc =
  if-[]-complete (masterCoherentᵇ sigs) _
    (Equivalence.from T-≡ (masterCoherentᵇ-complete sigs mc))

checkSigNamesUnique-complete : ∀ (sigs : List DBCSignal)
  → AllPairs _≢_ (map DBCSignal.name sigs) → checkSigNamesUnique sigs ≡ []
checkSigNamesUnique-complete sigs p =
  requireDec-complete (allPairs? (λ i j → ¬? (i ≟ᴵ j)) (map DBCSignal.name sigs)) _ p

checkMsgIdsUnique-complete : ∀ (msgs : List DBCMessage)
  → AllPairs _≢_ (map DBCMessage.id msgs) → checkMsgIdsUnique msgs ≡ []
checkMsgIdsUnique-complete msgs p =
  requireDec-complete (allPairs? (λ x y → ¬? (x ≟-CANId y)) (map DBCMessage.id msgs)) _ p

checkUnresolved-complete : ∀ (rvds : List RawValueDesc) → rvds ≡ [] → checkUnresolved rvds ≡ []
checkUnresolved-complete _ refl = refl

checkAttrs-complete : ∀ (attrs : List DBCAttribute)
  → All (WFAttribute (collectDefs attrs)) attrs → checkAttrs attrs ≡ []
checkAttrs-complete attrs wf =
  concatMap-≡[]-complete (All.map (λ {a} → attrIssues-complete (collectDefs attrs) a) wf)

checkTextMessage-complete : ∀ (m : DBCMessage) → MessageWF m → checkTextMessage m ≡ []
checkTextMessage-complete m wf =
  ++-≡[]-combine a-eq (++-≡[]-combine b-eq (++-≡[]-combine c-eq (++-≡[]-combine d-eq e-eq)))
  where
    sigs = DBCMessage.signals m
    fb   = dlcBytes (DBCMessage.dlc m)
    a-eq = checkSigNamesUnique-complete sigs (MessageWF.sig-names-unique wf)
    b-eq = mcIssue-complete sigs (MessageWF.mc wf)
    c-eq = concatMap-≡[]-complete
             (All.map (λ {s} → signalBounds-complete s) (MessageWF.wf-sigs wf))
    d-eq = concatMap-≡[]-complete
             (All.map (λ {s} p → pvGo-complete fb _ s p) (MessageWF.pvs wf))
    e-eq = concatMap-≡[]-complete
             (All.map (λ {s} p → pGo-complete (DBCSignal.presence s) _ p) (MessageWF.wfps wf))

wfTextIssues-complete : ∀ (d : DBC) → WellFormedTextDBCAgg d → wfTextIssues d ≡ []
wfTextIssues-complete d wf =
  ++-≡[]-combine
    (concatMap-≡[]-complete
      (All.map (λ {m} → checkTextMessage-complete m) (WellFormedTextDBCAgg.msg-wfs wf)))
    (++-≡[]-combine
      (checkMsgIdsUnique-complete (DBC.messages d) (WellFormedTextDBCAgg.msg-ids-unique wf))
      (++-≡[]-combine
        (checkAttrs-complete (DBC.attributes d) (WellFormedTextDBCAgg.attr-wfs wf))
        (checkUnresolved-complete (DBC.unresolvedValueDescs d)
          (WellFormedTextDBCAgg.unresolved-empty wf))))
