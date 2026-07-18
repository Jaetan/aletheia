-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Attribute soundness + completeness for the runtime checker
-- (`Aletheia.DBC.TextParser.WellFormedCheck`): pairs the `attrIssues`
-- dispatch with the `WFAttribute` predicate tree.  The checker's attribute
-- leaves are `Dec`-valued (`wfAttrType?` / `vmt?` / `enumOk?`) consumed via
-- `requireDec`, so each per-leaf direction lands through the shared
-- `requireDec-sound` / `requireDec-complete`; reached by the `Sound.agda`
-- facade.
module Aletheia.DBC.TextParser.Properties.WellFormedCheck.Sound.Attr where

open import Data.List using (List; [])
open import Data.Maybe using (nothing; just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Aletheia.DBC.Types using
  ( AttrDef; AttrDefault; AttrAssign
  ; DBCAttribute; DBCAttrDef; DBCAttrDefault; DBCAttrAssign )
open import Aletheia.DBC.TextParser.Attributes using (lookupDef)
open import Aletheia.DBC.TextParser.Properties.Aggregator.Foundations using
  (WFAttribute; wfDef; wfDefault; wfAssign)
open import Aletheia.DBC.Validity.Combinators using
  (requireDec-sound; requireDec-complete)
open import Aletheia.DBC.Validity.ListLemmas using (++-≡[]-split; ++-≡[]-combine)
open import Aletheia.DBC.TextParser.WellFormedCheck using
  (wfAttrType?; vmt?; enumOk?; attrIssues)

-- ── the 3-ctor WFAttribute dispatch (soundness) ──────────────────────────────
--
-- `attrIssues` dispatches on the `DBCAttribute` ctor; every leaf emits via
-- `requireDec`, so `requireDec-sound` lands each `WFAttribute` premise
-- directly.  For Default/Assign the `lookupDef` result is EXPOSED with
-- `with … in eq` — the `eq` is EXACTLY each WFAttribute ctor's `lookupDef …
-- ≡ just def` premise.  `nothing` refutes by absurd pattern:
-- `resolveDefIssues nothing …` is a non-empty singleton, so the `≡ []`
-- premise is a constructor clash.

attrIssues-sound : ∀ (defs : List AttrDef) (a : DBCAttribute)
  → attrIssues defs a ≡ [] → WFAttribute defs a
attrIssues-sound defs (DBCAttrDef d) premise =
  wfDef d (requireDec-sound (wfAttrType? (AttrDef.attrType d)) _ premise)
attrIssues-sound defs (DBCAttrAssign a) premise
  with lookupDef (AttrAssign.name a) defs in eq
... | just def = wfAssign a def eq
      (requireDec-sound (vmt? (AttrDef.attrType def) (AttrAssign.value a)) _ premise)
attrIssues-sound defs (DBCAttrAssign a) () | nothing
attrIssues-sound defs (DBCAttrDefault d) premise
  with lookupDef (AttrDefault.name d) defs in eq
... | just def =
  let (req , eeq) = ++-≡[]-split premise
  in wfDefault d def eq
       (requireDec-sound (vmt?    (AttrDef.attrType def) (AttrDefault.value d)) _ req)
       (requireDec-sound (enumOk? (AttrDef.attrType def) (AttrDefault.value d)) _ eeq)
attrIssues-sound defs (DBCAttrDefault d) () | nothing

-- ── the 3-ctor WFAttribute dispatch (completeness) ────────────────────────────
--
-- Match the `WFAttribute` ctor (which supplies `def` + the `lookupDef … ≡ just
-- def` proof); a SINGLE `rewrite lookup-eq` collapses `lookupDef … → just def`
-- in the goal (safe — `attrIssues` is list arithmetic, not a parser goal), then
-- each WF premise feeds `requireDec-complete` (+ `++-≡[]-combine` for the
-- Default arm's two parts).

attrIssues-complete : ∀ (defs : List AttrDef) (a : DBCAttribute)
  → WFAttribute defs a → attrIssues defs a ≡ []
attrIssues-complete defs (DBCAttrDef d) (wfDef .d wfty) =
  requireDec-complete (wfAttrType? (AttrDef.attrType d)) _ wfty
attrIssues-complete defs (DBCAttrAssign a) (wfAssign .a def lookup-eq vmt)
  rewrite lookup-eq =
  requireDec-complete (vmt? (AttrDef.attrType def) (AttrAssign.value a)) _ vmt
attrIssues-complete defs (DBCAttrDefault d) (wfDefault .d def lookup-eq vmt enum)
  rewrite lookup-eq = ++-≡[]-combine
    (requireDec-complete (vmt?    (AttrDef.attrType def) (AttrDefault.value d)) _ vmt)
    (requireDec-complete (enumOk? (AttrDef.attrType def) (AttrDefault.value d)) _ enum)
