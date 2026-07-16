-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Master-coherence soundness + completeness for the runtime checker
-- (`Aletheia.DBC.TextParser.WellFormedCheck`).  `mcGo` folds Bool `any`/`all`
-- over the signal list against `findMuxMaster`, so `mcGo-sound`/`-complete` need
-- Bool-`any`/`all` ⇔ `Any`/`All` reflection + a `findMuxMaster` characterization.
module Aletheia.DBC.TextParser.Properties.WellFormedCheck.Sound.Master where

open import Data.Bool using (T; true)
open import Data.Bool.Properties using (T-∧; T-≡)
open import Data.Char using (Char)
open import Data.List using (List)
open import Data.List.NonEmpty using (List⁺)
open import Data.List.Membership.Propositional using (find; lose)
open import Data.List.Relation.Unary.Any.Properties using (any⁻; any⁺)
open import Data.List.Relation.Unary.All using (map)
open import Data.List.Relation.Unary.All.Properties using (all⁺; all⁻)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Aletheia.DBC.Identifier using (Identifier; ≡csᵇ-sound; ≡csᵇ-complete)
open import Aletheia.DBC.Types using (DBCSignal; SignalPresence; Always; When)
open import Aletheia.DBC.Formatter.WellFormedText using (MasterCoherent; mc-no-mux; mc-mux)
open import Aletheia.DBC.TextFormatter.Topology using (findMuxMaster)
open import Aletheia.DBC.TextParser.WellFormedCheck using
  (isAlwaysᵇ; wGo; masterOkᵇ; whenOkᵇ; mcGo; masterCoherentᵇ)

-- ── presence leaves ──────────────────────────────────────────────────────────
--
-- `isAlwaysᵇ` / `wGo` are exposed on the `SignalPresence` scrutinee (no `with`),
-- so each bridge is a direct match.  `wGo-sound` returns the master-reference
-- fact in the SAME ∀-shape `MasterCoherent.mc-mux`'s slaves field carries
-- (Formatter/WellFormedText.agda, `mc-mux`), so the fold-level lemma can `All.map`
-- it per element; `wGo-complete` is its dual, feeding the completeness `all`.

isAlwaysᵇ-sound : ∀ (p : SignalPresence) → T (isAlwaysᵇ p) → p ≡ Always
isAlwaysᵇ-sound Always     _  = refl
isAlwaysᵇ-sound (When _ _) ()

isAlwaysᵇ-complete : ∀ (p : SignalPresence) → p ≡ Always → T (isAlwaysᵇ p)
isAlwaysᵇ-complete Always refl = tt

wGo-sound : ∀ (n : List Char) (p : SignalPresence) → T (wGo n p)
  → ∀ (m : Identifier) (vs : List⁺ ℕ) → p ≡ When m vs → Identifier.name m ≡ n
wGo-sound n Always      _  m vs ()
wGo-sound n (When m vs) tp .m .vs refl = ≡csᵇ-sound (Identifier.name m) n tp

wGo-complete : ∀ (n : List Char) (p : SignalPresence)
  → (∀ (m : Identifier) (vs : List⁺ ℕ) → p ≡ When m vs → Identifier.name m ≡ n)
  → T (wGo n p)
wGo-complete n Always      _ = tt
wGo-complete n (When m vs) f = ≡csᵇ-complete (Identifier.name m) n (f m vs refl)

-- ── the master fold (WF field `mc` = MasterCoherent) ────────────────────────
--
-- `mcGo` is exposed on `findMuxMaster`'s `Maybe (List Char)` result, so `mcGo-sound`
-- takes it as `mm` + the equation and matches structurally (no `with` anywhere in
-- this module — the top wrapper instantiates `mm := findMuxMaster sigs` with a
-- `refl` equation, dodging the `with`-abstraction hazard entirely).  The `just n`
-- case is the reflection chain: `≡ true → T` (`T-≡`), split the ∧ (`T-∧`), reflect
-- the Bool `any`/`all` (the `Data.Bool.ListAction` folds) into `Any`/`All` via
-- `any⁻`/`all⁺`, pull
-- the master out with `find` (keeps the `∈` witness `mc-mux` needs), split its
-- `masterOkᵇ` conjunct, then `≡csᵇ-sound`/`isAlwaysᵇ-sound`; `All.map wGo-sound`
-- lands the slaves field verbatim.

mcGo-sound : ∀ (mm : Maybe (List Char)) (sigs : List DBCSignal)
  → findMuxMaster sigs ≡ mm → mcGo mm sigs ≡ true → MasterCoherent sigs
mcGo-sound nothing  sigs eq _      = mc-no-mux eq
mcGo-sound (just n) sigs eq mcGoeq =
  mc-mux n eq ms ms∈sigs nameEq presEq slaves
  where
    tconj = Equivalence.from T-≡ mcGoeq          -- T (any (masterOkᵇ n) sigs ∧ all (whenOkᵇ n) sigs)
    tAny  = proj₁ (Equivalence.to T-∧ tconj)     -- T (any (masterOkᵇ n) sigs)
    tAll  = proj₂ (Equivalence.to T-∧ tconj)     -- T (all (whenOkᵇ n) sigs)
    found = find (any⁻ (masterOkᵇ n) sigs tAny)  -- ∃ x → x ∈ sigs × T (masterOkᵇ n x)
    ms      = proj₁ found
    ms∈sigs = proj₁ (proj₂ found)
    splitOk = Equivalence.to T-∧ (proj₂ (proj₂ found))  -- T (name ≡csᵇ n) × T (isAlwaysᵇ presence)
    nameEq  = ≡csᵇ-sound (Identifier.name (DBCSignal.name ms)) n (proj₁ splitOk)
    presEq  = isAlwaysᵇ-sound (DBCSignal.presence ms) (proj₂ splitOk)
    slaves  = map (λ {s} tw → wGo-sound n (DBCSignal.presence s) tw)
                  (all⁺ (whenOkᵇ n) sigs tAll)

-- Completeness dual.  Both `findMuxMaster` equations pin `mm` (via `trans (sym eq)
-- …`), then `rewrite` collapses the goal so `mcGo mm sigs` reduces (safe — mcGo is
-- a Bool fold, not a parser goal).  `mc-mux` rebuilds the conjunction from the
-- reverse lemmas: `any⁺ ∘ lose` (master back into the Bool `any`) and `all⁻ ∘
-- map wGo-complete` (slaves back into the Bool `all`), joined by `T-∧`, then `T-≡`.

mcGo-complete : ∀ (mm : Maybe (List Char)) (sigs : List DBCSignal)
  → findMuxMaster sigs ≡ mm → MasterCoherent sigs → mcGo mm sigs ≡ true
mcGo-complete mm sigs eq (mc-no-mux eq-nothing) rewrite trans (sym eq) eq-nothing = refl
mcGo-complete mm sigs eq (mc-mux masterName eq-just ms ms∈sigs nameEq presEq slaves)
  rewrite trans (sym eq) eq-just =
  Equivalence.to T-≡ (Equivalence.from T-∧ (tAny , tAll))
  where
    tName     = ≡csᵇ-complete (Identifier.name (DBCSignal.name ms)) masterName nameEq
    tAlways   = isAlwaysᵇ-complete (DBCSignal.presence ms) presEq
    tMasterOk = Equivalence.from T-∧ (tName , tAlways)      -- T (masterOkᵇ masterName ms)
    tAny      = any⁺ (masterOkᵇ masterName) (lose ms∈sigs tMasterOk)
    tAll      = all⁻ (whenOkᵇ masterName)
                  (map (λ {s} f → wGo-complete masterName (DBCSignal.presence s) f) slaves)

-- ── top wrappers ─────────────────────────────────────────────────────────────
--
-- `masterCoherentᵇ sigs = mcGo (findMuxMaster sigs) sigs` DEFINITIONALLY, so the
-- wrapper just instantiates `mm := findMuxMaster sigs` and hands `mcGo-sound/-complete`
-- a `refl` for the `findMuxMaster sigs ≡ mm` equation — no `with` (the equation is
-- an explicit lemma argument precisely to enable this).  `Sound.agda` consumes
-- these through the `mcIssue` `if`-elim.

masterCoherentᵇ-sound : ∀ (sigs : List DBCSignal)
  → masterCoherentᵇ sigs ≡ true → MasterCoherent sigs
masterCoherentᵇ-sound sigs eq = mcGo-sound (findMuxMaster sigs) sigs refl eq

masterCoherentᵇ-complete : ∀ (sigs : List DBCSignal)
  → MasterCoherent sigs → masterCoherentᵇ sigs ≡ true
masterCoherentᵇ-complete sigs mc = mcGo-complete (findMuxMaster sigs) sigs refl mc
