-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Discharge the per-section name-stop fields of
-- `WellFormedTextDBCAgg` from `Identifier` validity, leaving only the two
-- heavy fields (`MessageWF`, `WFAttribute`) and the two validator-backed
-- fields (`msg-ids-unique`, `unresolved-empty`) as hypotheses.
--
-- Every `*NameStop` predicate is the SAME Σ-shape on an `Identifier`:
--
--   Σ[ c ∈ Char ] Σ[ cs ∈ List Char ]
--     (Identifier.name i ≡ c ∷ cs) × (isHSpace c ≡ false)
--
-- and every such predicate is discharged UNIVERSALLY: an `Identifier`'s
-- `valid : T (validIdentifierᵇ name)` rules out the empty name
-- (`validIdentifierᵇ [] = false`, so `valid : T false` is impossible) and
-- exposes `T (isIdentStart c)` for the head, which `isIdentStart→¬isHSpace`
-- (Properties.CharClassDisjoint) turns into `isHSpace c ≡ false`.  This is
-- the same one-liner as
-- `…Aggregator.Dispatcher.Attribute.Foundations.identifier-name-stop`,
-- generalised across the five remaining sections.
--
-- Scope (DEFERRED_ITEMS.md E.2 "bounded slice"): the five name-stop record
-- fields auto-derive; `wellFormedFromValidity` proves the cascade composes
-- by reducing the `WellFormedTextDBCAgg` precondition from nine fields to
-- the four that genuinely carry content beyond Identifier-validity — the
-- two heavy proofs (`MessageWF` per-signal aggregation, `WFAttribute`
-- BA_DEF_ typing) and the two validator-backed fields (CHECK 18
-- `msg-ids-unique`, CHECK 23 `unresolved-empty`).  Those four remain
-- hypotheses here; closing them is the reassessment point.
module Aletheia.DBC.TextParser.Properties.WellFormedFromValidity where

open import Data.Bool using (Bool; true; false; T; _∧_)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Aletheia.DBC.Identifier using (Identifier; mkIdent)
open import Aletheia.DBC.Types using
  ( DBC; DBCMessage; Node; ValueTable; EnvironmentVar; DBCSignal; SignalGroup
  ; DBCComment; CTNetwork; CTNode; CTMessage; CTSignal; CTEnvVar )

open import Aletheia.DBC.TextParser.Lexer using (isHSpace)
open import Aletheia.DBC.TextParser.Properties.CharClassDisjoint using
  (isIdentStart→¬isHSpace)

open import Aletheia.DBC.TextParser.Format.Nodes using (NodeNameStop)
open import Aletheia.DBC.TextParser.Format.ValueTable using (ValueTableNameStop)
open import Aletheia.DBC.TextParser.Format.EnvVar using (EnvVarNameStop)
open import Aletheia.DBC.TextParser.Format.Comments using (CommentTargetStop)
open import Aletheia.DBC.TextParser.Format.SignalGroup using
  (SignalGroupNameStop; SigNameStop)
open import Aletheia.DBC.TextParser.Properties.SignalGroups.SignalGroup using
  (SignalGroupWF)
open import Aletheia.DBC.TextParser.Properties.Topology.Signal using (SignalNameStop)
open import Aletheia.DBC.TextParser.Properties.Topology using (MessageWF)
open import Aletheia.DBC.TextParser.Properties.Aggregator.Foundations using
  (WFAttribute)
open import Aletheia.DBC.TextFormatter.Attributes using (collectDefs)
open import Aletheia.DBC.TextParser.WellFormed using (WellFormedTextDBCAgg)

private
  -- `T (a ∧ b) → T a` by closed-Bool reduction: only the (true, true) case
  -- is inhabited (`T (false ∧ _) = T false = ⊥`), and `(true ∧ b) = b`, so
  -- the conclusion `T a = T true = ⊤`.  Mirrors the splitter in
  -- …Attribute.Foundations; kept local to stay off the attribute subtree.
  T-∧₁ : ∀ {a b : Bool} → T (a ∧ b) → T a
  T-∧₁ {true} {true} _ = tt

-- Generic universal name-stop.  `validIdentifierᵇ (c ∷ cs)`'s first conjunct
-- is `isIdentStart c`, so `T-∧₁ valid : T (isIdentStart c)`; the empty-name
-- case is closed by `()` on `valid : T (validIdentifierᵇ []) = T false`.
identNameStop : ∀ (i : Identifier)
  → Σ[ c ∈ Char ] Σ[ cs ∈ List Char ]
      (Identifier.name i ≡ c ∷ cs) × (isHSpace c ≡ false)
identNameStop (mkIdent []       ())
identNameStop (mkIdent (c ∷ cs) v) =
  c , cs , refl , isIdentStart→¬isHSpace c (T-∧₁ v)

-- ── Per-section discharges (each `*NameStop` unfolds to the Σ above) ──────

nodeNameStop : ∀ (n : Node) → NodeNameStop n
nodeNameStop n = identNameStop (Node.name n)

valueTableNameStop : ∀ (vt : ValueTable) → ValueTableNameStop vt
valueTableNameStop vt = identNameStop (ValueTable.name vt)

envVarNameStop : ∀ (ev : EnvironmentVar) → EnvVarNameStop ev
envVarNameStop ev = identNameStop (EnvironmentVar.name ev)

signalNameStop : ∀ (sig : DBCSignal) → SignalNameStop sig
signalNameStop sig = identNameStop (DBCSignal.name sig)

signalGroupNameStop : ∀ (sg : SignalGroup) → SignalGroupNameStop sg
signalGroupNameStop sg = identNameStop (SignalGroup.name sg)

sigNameStop : ∀ (i : Identifier) → SigNameStop i
sigNameStop i = identNameStop i

-- `SignalGroupWF` is a 2-field record: the group's own name-stop plus a
-- per-member-signal stop (`SignalGroup.signals : List Identifier`).
signalGroupWF : ∀ (sg : SignalGroup) → SignalGroupWF sg
signalGroupWF sg = record
  { name-stop  = signalGroupNameStop sg
  ; sigs-stops = All.universal sigNameStop (SignalGroup.signals sg)
  }

-- `CommentTargetStop` splits on the comment target: ⊤ for the
-- Identifier-free constructors (Network / Message), a name-stop otherwise.
commentTargetStop : ∀ (c : DBCComment) → CommentTargetStop c
commentTargetStop c with DBCComment.target c
... | CTNetwork    = tt
... | CTNode n     = identNameStop n
... | CTMessage _  = tt
... | CTSignal _ s = identNameStop s
... | CTEnvVar ev  = identNameStop ev

-- ── Cascade composition ──────────────────────────────────────────────────
--
-- The five name-stop record fields auto-derive from Identifier-validity, so
-- the `WellFormedTextDBCAgg` precondition collapses to the four fields that
-- carry genuine content: the two heavy proofs (`MessageWF`, `WFAttribute`)
-- and the two validator-backed fields (`msg-ids-unique` ← CHECK 1,
-- `unresolved-empty` ← CHECK 23).  Discharging those four is the
-- reassessment point (DEFERRED_ITEMS.md E.2); they remain hypotheses here.
wellFormedFromValidity : ∀ (d : DBC)
  → All MessageWF (DBC.messages d)
  → All (WFAttribute (collectDefs (DBC.attributes d))) (DBC.attributes d)
  → AllPairs _≢_ (map DBCMessage.id (DBC.messages d))
  → DBC.unresolvedValueDescs d ≡ []
  → WellFormedTextDBCAgg d
wellFormedFromValidity d msg-wfs attr-wfs ids unres = record
  { node-stops       = All.universal nodeNameStop        (DBC.nodes           d)
  ; vt-stops         = All.universal valueTableNameStop  (DBC.valueTables     d)
  ; msg-wfs          = msg-wfs
  ; ev-stops         = All.universal envVarNameStop      (DBC.environmentVars d)
  ; cm-stops         = All.universal commentTargetStop   (DBC.comments        d)
  ; attr-wfs         = attr-wfs
  ; sg-wfs           = All.universal signalGroupWF       (DBC.signalGroups    d)
  ; msg-ids-unique   = ids
  ; unresolved-empty = unres
  }
