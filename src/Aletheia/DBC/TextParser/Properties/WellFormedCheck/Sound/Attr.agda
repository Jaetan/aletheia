-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Attribute-leaf soundness + completeness for the E.2 route (b) runtime checker
-- (`Aletheia.DBC.TextParser.WellFormedCheck`).  Bridges the checker's attribute
-- leaves (`vmtᵇ`, `enumOkᵇ`, `wfAttrTypeIssues`, and the `attrIssues` dispatch)
-- to the `WFAttribute` predicate tree (E2_ROUTE_B.md §5.3); reached by the
-- `Sound.agda` facade (added to `proofModules` at S1.6).
--
-- Built in sub-chunks, each type-checked standalone:
--   S1.5a  `vmtᵇ-sound` / `-complete`            (value ↔ type match)  (this file, first)
--   S1.5b  `enumOkᵇ-sound` / `-complete`         (enum-default stability)
--   S1.5c  `wfAttrTypeIssues-sound` / `-complete`(attr-type well-formedness)
--   S1.5d  `attrIssues-sound` / `-complete`      (the 3-ctor WFAttribute dispatch)
module Aletheia.DBC.TextParser.Properties.WellFormedCheck.Sound.Attr where

open import Data.Bool using (T; Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (toWitness; fromWitness)

open import Aletheia.DBC.Types using
  ( AttrType; ATInt; ATFloat; ATString; ATEnum; ATHex
  ; AttrValue; AVInt; AVFloat; AVString; AVEnum; AVHex
  ; DBCAttribute; DBCAttrDef; DBCAttrDefault; DBCAttrAssign
  ; AttrDef; AttrDefault; AttrAssign; ValidationIssue )
open import Aletheia.DBC.TextParser.Attributes using (lookupDef)
open import Aletheia.DBC.TextParser.Properties.Attributes.Common using
  (ValueMatchesType; VMTInt; VMTFloat; VMTString; VMTEnum; VMTHex)
open import Aletheia.DBC.TextParser.Properties.Attributes.Def using
  (WfAttrType; WfATInt; WfATFloat; WfATString; WfATEnum; WfATHex)
open import Aletheia.DBC.TextParser.Properties.Aggregator.Foundations using
  (DefaultEnumOK; WFAttribute; wfDef; wfDefault; wfAssign)
open import Aletheia.DBC.Validity.ListLemmas using (++-≡[]-split; ++-≡[]-combine)
open import Aletheia.DBC.TextParser.WellFormedCheck using
  (vmtᵇ; enumOkᵇ; wfAttrTypeIssues; attrIssues)

-- ── value/type match (WFAttribute conjunct `ValueMatchesType`) ────────────────
--
-- `vmtᵇ` is `true` on exactly the 5 diagonal `AT*`↔`AV*` pairs, `false` elsewhere.
-- `ValueMatchesType` has exactly those 5 constructors, so soundness is the 5×5
-- double-match: the diagonal returns the constructor (carrying the value witness),
-- the 20 off-diagonal pairs reduce `vmtᵇ` to `false` so `T false = ⊥` refutes by `()`.

vmtᵇ-sound : ∀ (t : AttrType) (v : AttrValue) → T (vmtᵇ t v) → ValueMatchesType t v
vmtᵇ-sound (ATInt _ _)   (AVInt z)    _ = VMTInt z
vmtᵇ-sound (ATFloat _ _) (AVFloat d)  _ = VMTFloat d
vmtᵇ-sound ATString      (AVString s) _ = VMTString s
vmtᵇ-sound (ATEnum _)    (AVEnum n)   _ = VMTEnum n
vmtᵇ-sound (ATHex _ _)   (AVHex n)    _ = VMTHex n
vmtᵇ-sound (ATInt _ _)   (AVFloat _)  ()
vmtᵇ-sound (ATInt _ _)   (AVString _) ()
vmtᵇ-sound (ATInt _ _)   (AVEnum _)   ()
vmtᵇ-sound (ATInt _ _)   (AVHex _)    ()
vmtᵇ-sound (ATFloat _ _) (AVInt _)    ()
vmtᵇ-sound (ATFloat _ _) (AVString _) ()
vmtᵇ-sound (ATFloat _ _) (AVEnum _)   ()
vmtᵇ-sound (ATFloat _ _) (AVHex _)    ()
vmtᵇ-sound ATString      (AVInt _)    ()
vmtᵇ-sound ATString      (AVFloat _)  ()
vmtᵇ-sound ATString      (AVEnum _)   ()
vmtᵇ-sound ATString      (AVHex _)    ()
vmtᵇ-sound (ATEnum _)    (AVInt _)    ()
vmtᵇ-sound (ATEnum _)    (AVFloat _)  ()
vmtᵇ-sound (ATEnum _)    (AVString _) ()
vmtᵇ-sound (ATEnum _)    (AVHex _)    ()
vmtᵇ-sound (ATHex _ _)   (AVInt _)    ()
vmtᵇ-sound (ATHex _ _)   (AVFloat _)  ()
vmtᵇ-sound (ATHex _ _)   (AVString _) ()
vmtᵇ-sound (ATHex _ _)   (AVEnum _)   ()

-- Completeness: matching the `ValueMatchesType` constructor forces (t,v) onto the
-- diagonal, where `vmtᵇ` reduces to `true` (`T true = ⊤`), so 5 clauses suffice.
vmtᵇ-complete : ∀ (t : AttrType) (v : AttrValue) → ValueMatchesType t v → T (vmtᵇ t v)
vmtᵇ-complete (ATInt _ _)   (AVInt _)    (VMTInt _)    = tt
vmtᵇ-complete (ATFloat _ _) (AVFloat _)  (VMTFloat _)  = tt
vmtᵇ-complete ATString      (AVString _) (VMTString _) = tt
vmtᵇ-complete (ATEnum _)    (AVEnum _)   (VMTEnum _)   = tt
vmtᵇ-complete (ATHex _ _)   (AVHex _)    (VMTHex _)    = tt

-- ── enum-default stability (WFAttribute conjunct `DefaultEnumOK`) ─────────────
--
-- `DefaultEnumOK t v` is `⊤` for every (t,v) EXCEPT (ATEnum labels, AVEnum n),
-- where it is the owed bridge `findLabel (nthLabel n labels) labels ≡ just n` —
-- exactly the proposition `enumOkᵇ`'s `Dec` decides.  Since `enumOkᵇ (ATEnum …)
-- (AVEnum …) = ⌊ dec ⌋` and `⌊_⌋ = isYes`, `T ⌊ dec ⌋ = True dec`, so `toWitness`
-- extracts the proof (soundness) and `fromWitness` re-decides it (completeness).
-- No catch-all — and crucially MATCH `t` (the AttrType) FIRST: `DefaultEnumOK`
-- matches arg1 first, so it stays STUCK under a variable AttrType even when the
-- AttrValue already rules out the enum clause.  With `t` concrete, a non-ATEnum
-- type reduces `DefaultEnumOK t v` to `⊤` for ANY v; only `ATEnum` needs the v-split.

enumOkᵇ-sound : ∀ (t : AttrType) (v : AttrValue) → T (enumOkᵇ t v) → DefaultEnumOK t v
enumOkᵇ-sound (ATInt _ _)     _           _  = tt
enumOkᵇ-sound (ATFloat _ _)   _           _  = tt
enumOkᵇ-sound ATString        _           _  = tt
enumOkᵇ-sound (ATHex _ _)     _           _  = tt
enumOkᵇ-sound (ATEnum labels) (AVEnum n)  tw = toWitness tw
enumOkᵇ-sound (ATEnum _)      (AVInt _)    _  = tt
enumOkᵇ-sound (ATEnum _)      (AVFloat _)  _  = tt
enumOkᵇ-sound (ATEnum _)      (AVString _) _  = tt
enumOkᵇ-sound (ATEnum _)      (AVHex _)    _  = tt

enumOkᵇ-complete : ∀ (t : AttrType) (v : AttrValue) → DefaultEnumOK t v → T (enumOkᵇ t v)
enumOkᵇ-complete (ATInt _ _)     _           _   = tt
enumOkᵇ-complete (ATFloat _ _)   _           _   = tt
enumOkᵇ-complete ATString        _           _   = tt
enumOkᵇ-complete (ATHex _ _)     _           _   = tt
enumOkᵇ-complete (ATEnum labels) (AVEnum n)  deq = fromWitness deq
enumOkᵇ-complete (ATEnum _)      (AVInt _)    _   = tt
enumOkᵇ-complete (ATEnum _)      (AVFloat _)  _   = tt
enumOkᵇ-complete (ATEnum _)      (AVString _) _   = tt
enumOkᵇ-complete (ATEnum _)      (AVHex _)    _   = tt

-- ── attr-type well-formedness (WFAttribute `wfDef` conjunct `WfAttrType`) ─────
--
-- `wfAttrTypeIssues` emits `AttributeEnumEmpty` on exactly `ATEnum []`, `[]`
-- elsewhere; `WfAttrType` accepts every type EXCEPT the empty enum.  Match `t`
-- first (arg-order discipline).  Soundness: the `ATEnum []` clause is refuted by
-- `()` (the emitted singleton `≢ []`); completeness matches the `WfAT*` ctor.

wfAttrTypeIssues-sound : ∀ (t : AttrType) → wfAttrTypeIssues t ≡ [] → WfAttrType t
wfAttrTypeIssues-sound (ATInt mn mx)     _ = WfATInt mn mx
wfAttrTypeIssues-sound (ATFloat mn mx)   _ = WfATFloat mn mx
wfAttrTypeIssues-sound ATString          _ = WfATString
wfAttrTypeIssues-sound (ATEnum (x ∷ xs)) _ = WfATEnum x xs
wfAttrTypeIssues-sound (ATEnum [])       ()
wfAttrTypeIssues-sound (ATHex mn mx)     _ = WfATHex mn mx

wfAttrTypeIssues-complete : ∀ (t : AttrType) → WfAttrType t → wfAttrTypeIssues t ≡ []
wfAttrTypeIssues-complete (ATInt _ _)      (WfATInt _ _)   = refl
wfAttrTypeIssues-complete (ATFloat _ _)    (WfATFloat _ _) = refl
wfAttrTypeIssues-complete ATString         WfATString      = refl
wfAttrTypeIssues-complete (ATEnum (_ ∷ _)) (WfATEnum _ _)  = refl
wfAttrTypeIssues-complete (ATHex _ _)      (WfATHex _ _)   = refl

-- ── the 3-ctor WFAttribute dispatch (soundness) ──────────────────────────────
--
-- `resolveDefIssues`/`enumDefaultIssue` emit via `if bool then [] else (issue ∷ [])`;
-- `if-[]-sound` is the Bool-`if` eliminator.  `attrIssues-sound` dispatches on the
-- `DBCAttribute` ctor; for Default/Assign it EXPOSES the `lookupDef` result with
-- `with … in eq` — the `eq` is EXACTLY each WFAttribute ctor's `lookupDef … ≡ just
-- def` premise.  `nothing` refutes: `resolveDefIssues nothing …` is a non-empty
-- singleton, `≢ []`.

private
  ∷≢[] : ∀ {A : Set} {x : A} {xs : List A} → x ∷ xs ≡ [] → ⊥
  ∷≢[] ()

if-[]-sound : ∀ (b : Bool) (i : ValidationIssue)
  → (if b then [] else (i ∷ [])) ≡ [] → T b
if-[]-sound true  _ _  = tt
if-[]-sound false _ ()

attrIssues-sound : ∀ (defs : List AttrDef) (a : DBCAttribute)
  → attrIssues defs a ≡ [] → WFAttribute defs a
attrIssues-sound defs (DBCAttrDef d) premise =
  wfDef d (wfAttrTypeIssues-sound (AttrDef.attrType d) premise)
attrIssues-sound defs (DBCAttrAssign a) premise
  with lookupDef (AttrAssign.name a) defs in eq
... | just def = wfAssign a def eq
      (vmtᵇ-sound (AttrDef.attrType def) (AttrAssign.value a) (if-[]-sound _ _ premise))
... | nothing  = ⊥-elim (∷≢[] premise)
attrIssues-sound defs (DBCAttrDefault d) premise
  with lookupDef (AttrDefault.name d) defs in eq
... | nothing  = ⊥-elim (∷≢[] premise)
... | just def with ++-≡[]-split premise
...   | (req , eeq) = wfDefault d def eq
        (vmtᵇ-sound    (AttrDef.attrType def) (AttrDefault.value d) (if-[]-sound _ _ req))
        (enumOkᵇ-sound (AttrDef.attrType def) (AttrDefault.value d) (if-[]-sound _ _ eeq))

-- ── the 3-ctor WFAttribute dispatch (completeness) ────────────────────────────
--
-- Match the `WFAttribute` ctor (which supplies `def` + the `lookupDef … ≡ just def`
-- proof); a SINGLE `rewrite lookup-eq` collapses `lookupDef … → just def` in the
-- goal (safe — `attrIssues` is list arithmetic, not a parser goal), then the
-- already-proven `vmtᵇ-complete`/`enumOkᵇ-complete`/`wfAttrTypeIssues-complete`
-- leaves feed `if-[]-complete` (+ `++-≡[]-combine` for the Default arm's two parts).

if-[]-complete : ∀ (b : Bool) (i : ValidationIssue)
  → T b → (if b then [] else (i ∷ [])) ≡ []
if-[]-complete true  _ _ = refl
if-[]-complete false _ ()

attrIssues-complete : ∀ (defs : List AttrDef) (a : DBCAttribute)
  → WFAttribute defs a → attrIssues defs a ≡ []
attrIssues-complete defs (DBCAttrDef d) (wfDef .d wfty) =
  wfAttrTypeIssues-complete (AttrDef.attrType d) wfty
attrIssues-complete defs (DBCAttrAssign a) (wfAssign .a def lookup-eq vmt)
  rewrite lookup-eq =
  if-[]-complete _ _ (vmtᵇ-complete (AttrDef.attrType def) (AttrAssign.value a) vmt)
attrIssues-complete defs (DBCAttrDefault d) (wfDefault .d def lookup-eq vmt enum)
  rewrite lookup-eq = ++-≡[]-combine
    (if-[]-complete _ _ (vmtᵇ-complete    (AttrDef.attrType def) (AttrDefault.value d) vmt))
    (if-[]-complete _ _ (enumOkᵇ-complete (AttrDef.attrType def) (AttrDefault.value d) enum))
