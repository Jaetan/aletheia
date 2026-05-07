{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4c — Combined per-section dispatcher.
--
-- Bundles the six per-section parseTopStmt-on-emit-* slims (5 simple +
-- TAT) into one universal lemma over the typed shadow `TopStmtTyped`,
-- gated by the `TopStmtTypedWF defs` predicate that bundles each
-- section's per-element precondition.
--
-- This module is the input to `ManyTopStmts.agda`'s
-- `many-η-roundtrip-with-lift` instantiation: the dispatcher is the
-- `P-on-emit` parameter, `TopStmtTypedWF defs` is the `Stop` parameter,
-- and the nonzero / head-not-newline emitter facts factor through the
-- existing per-section emitter-shape lemmas (with the TAT case routed
-- through the β prefix witness from `Attribute/PrefixHead.agda`).
module Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher where

open import Data.Char  using (Char)
open import Data.List  using (List; []; _∷_; length)
  renaming (_++_ to _++ₗ_)
open import Data.Maybe using (just)
open import Data.Nat   using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)

open import Aletheia.Parser.Combinators using
  (Position; ParseResult; mkResult; advancePositions)

open import Aletheia.DBC.Types using
  ( DBCMessage; ValueTable; EnvironmentVar; DBCComment; SignalGroup
  ; AttrDef; DBCAttribute
  )

open import Aletheia.DBC.TextParser.ValueTables using (RawValueDesc)

open import Aletheia.DBC.TextParser.TopLevel using
  (TopStmt; parseTopStmt)

open import Aletheia.DBC.TextFormatter.Attributes using
  (emitAttribute-chars)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart)

-- Per-section WF predicates (one per typed-shadow constructor).
open import Aletheia.DBC.TextParser.Properties.ValueTables using
  (ValueTableNameStop)
open import Aletheia.DBC.TextParser.Properties.Topology using
  (MessageWF)
open import Aletheia.DBC.TextParser.Properties.EnvVars using
  (EnvVarNameStop)
open import Aletheia.DBC.TextParser.Properties.Comments using
  (CommentTargetStop)
open import Aletheia.DBC.TextParser.Properties.SignalGroups using
  (SignalGroupWF)
open import Aletheia.DBC.TextParser.Properties.ValueTables.ValueDesc using
  (RawValueDescStop)

-- Foundations: typed shadow + lift + emitter + WFAttribute.
open import Aletheia.DBC.TextParser.Properties.Aggregator.Foundations using
  ( TopStmtTyped; TVT; TM; TEV; TCM; TAT; TSG; TVD
  ; emitTopStmt-chars
  ; liftTopStmt
  ; WFAttribute
  )

-- Per-section emitter-shape lemmas (nonzero + head-not-newline).
open import Aletheia.DBC.TextParser.Properties.ValueTables.ValueTable using
  (emitValueTable-chars-nonzero; emitValueTable-chars-head-not-newline)
open import Aletheia.DBC.TextParser.Properties.Topology.Message using
  (emitMessage-chars-nonzero; emitMessage-chars-head-not-newline)
open import Aletheia.DBC.TextParser.Properties.EnvVars.EnvVar using
  (emitEnvVar-chars-nonzero; emitEnvVar-chars-head-not-newline)
open import Aletheia.DBC.TextParser.Properties.Comments.Comment using
  (emitComment-chars-nonzero; emitComment-chars-head-not-newline)
open import Aletheia.DBC.TextParser.Properties.SignalGroups.SignalGroup using
  (emitSignalGroup-chars-nonzero; emitSignalGroup-chars-head-not-newline)

-- Per-section parseTopStmt-on-emit-* slims (existing dispatchers).
open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Simple using
  ( parseTopStmt-on-emit-TVT-eq
  ; parseTopStmt-on-emit-TM-eq
  ; parseTopStmt-on-emit-TEV-eq
  ; parseTopStmt-on-emit-TCM-eq
  ; parseTopStmt-on-emit-TSG-eq
  ; parseTopStmt-on-emit-TVD-eq
  )
open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.TopStmt using
  (parseTopStmt-on-emit-typed-TAT)

-- TAT β prefix witness.
open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.PrefixHead using
  (emitAttribute-chars-BA-head)

-- ============================================================================
-- WF PREDICATE FOR TYPED SHADOW
-- ============================================================================
--
-- One ctor per `TopStmtTyped` constructor, carrying that section's slim
-- precondition.  Indexed on `defs` because the TAT case's `WFAttribute`
-- depends on `defs`.

-- Phase E.5β: 7-ctor predicate; one per `TopStmtTyped` constructor,
-- carrying that section's slim precondition.  Indexed on `defs` because
-- the TAT case's `WFAttribute` depends on `defs`.
--
-- E.5α had this at 6 ctors with TVD-case absurd-elim.  E.5β promotes
-- the absurd-elim to a real `wfTVD` ctor + per-section roundtrip via
-- `parseTopStmt-on-emit-TVD-eq`.  At E.5β closure no `wfTVD` is ever
-- constructed at the universal-proof level (because `toTopStmtsTyped`
-- doesn't yet emit `TVD` — that wires in at E.7); the dispatcher and
-- WF predicate are infrastructure-ready for E.7's typed-shadow walk
-- extension.
data TopStmtTypedWF (defs : List AttrDef) : TopStmtTyped → Set where
  wfTVT : ∀ vt  → ValueTableNameStop vt → TopStmtTypedWF defs (TVT vt)
  wfTM  : ∀ msg → MessageWF msg         → TopStmtTypedWF defs (TM  msg)
  wfTEV : ∀ ev  → EnvVarNameStop ev     → TopStmtTypedWF defs (TEV ev)
  wfTCM : ∀ cm  → CommentTargetStop cm  → TopStmtTypedWF defs (TCM cm)
  wfTAT : ∀ a   → WFAttribute defs a    → TopStmtTypedWF defs (TAT a)
  wfTSG : ∀ sg  → SignalGroupWF sg      → TopStmtTypedWF defs (TSG sg)
  wfTVD : ∀ rvd → RawValueDescStop rvd  → TopStmtTypedWF defs (TVD rvd)

-- ============================================================================
-- COMBINED PER-SECTION DISPATCHER
-- ============================================================================
--
-- 6-way dispatch on the `TopStmtTyped` constructor.  Each case routes
-- to the existing per-section slim under its WF witness.

parseTopStmt-on-emitTopStmt-chars :
    ∀ (defs : List AttrDef) (pos : Position)
      (t : TopStmtTyped) (outer : List Char)
  → TopStmtTypedWF defs t
  → SuffixStops isNewlineStart outer
  → parseTopStmt pos (emitTopStmt-chars defs t ++ₗ outer)
    ≡ just (mkResult (liftTopStmt defs t)
                     (advancePositions pos (emitTopStmt-chars defs t))
                     outer)
parseTopStmt-on-emitTopStmt-chars defs pos (TVT vt)  outer (wfTVT _ ns)  ss-NL =
  parseTopStmt-on-emit-TVT-eq pos vt outer ns ss-NL
parseTopStmt-on-emitTopStmt-chars defs pos (TM  msg) outer (wfTM  _ wf)  ss-NL =
  parseTopStmt-on-emit-TM-eq pos msg outer wf ss-NL
parseTopStmt-on-emitTopStmt-chars defs pos (TEV ev)  outer (wfTEV _ ns)  ss-NL =
  parseTopStmt-on-emit-TEV-eq pos ev outer ns ss-NL
parseTopStmt-on-emitTopStmt-chars defs pos (TCM cm)  outer (wfTCM _ ts)  ss-NL =
  parseTopStmt-on-emit-TCM-eq pos cm outer ts ss-NL
parseTopStmt-on-emitTopStmt-chars defs pos (TAT a)   outer (wfTAT _ wfa) ss-NL =
  parseTopStmt-on-emit-typed-TAT defs pos a outer wfa ss-NL
parseTopStmt-on-emitTopStmt-chars defs pos (TSG sg)  outer (wfTSG _ wf)  ss-NL =
  parseTopStmt-on-emit-TSG-eq pos sg outer wf ss-NL
-- Phase E.5β: real TVD dispatcher proof via `parseTopStmt-on-emit-TVD-
-- eq` (V-bucket right arm; LEFT arm parseValueTable fails on VAL_-
-- prefix input via `alt-right-nothing`, RIGHT arm succeeds via the
-- slim parseValueDescription-roundtrip).  Replaces E.5α's absurd-elim.
parseTopStmt-on-emitTopStmt-chars defs pos (TVD rvd) outer (wfTVD _ rs) ss-NL =
  parseTopStmt-on-emit-TVD-eq pos rvd outer rs ss-NL

-- ============================================================================
-- EMITTER-SHAPE LEMMAS — uniform over `TopStmtTyped`
-- ============================================================================
--
-- 5 of 6 cases reduce by their existing per-section emitter-shape
-- lemma.  TAT case factors through the β prefix witness because
-- `emitAttribute-chars` does not reduce to a `_ ∷ _` head without case-
-- splitting on scope/target.

emitTopStmt-chars-nonzero :
    ∀ defs (t : TopStmtTyped) → 0 < length (emitTopStmt-chars defs t)
emitTopStmt-chars-nonzero _    (TVT vt)  = emitValueTable-chars-nonzero vt
emitTopStmt-chars-nonzero _    (TM  msg) = emitMessage-chars-nonzero msg
emitTopStmt-chars-nonzero _    (TEV ev)  = emitEnvVar-chars-nonzero ev
emitTopStmt-chars-nonzero _    (TCM cm)  = emitComment-chars-nonzero cm
emitTopStmt-chars-nonzero defs (TAT a)   =
  subst (λ xs → 0 < length xs)
        (sym (proj₂ (emitAttribute-chars-BA-head defs a)))
        (s≤s z≤n)
emitTopStmt-chars-nonzero _    (TSG sg)  = emitSignalGroup-chars-nonzero sg
-- Phase E.5α: `emitValueDescription-chars rvd` starts with `toList
-- "VAL_ " = 'V' ∷ 'A' ∷ 'L' ∷ '_' ∷ ' ' ∷ []`, so length is at least 5.
emitTopStmt-chars-nonzero _    (TVD _)   = s≤s z≤n

emitTopStmt-chars-head-not-newline :
    ∀ defs (t : TopStmtTyped) (suffix : List Char)
  → SuffixStops isNewlineStart (emitTopStmt-chars defs t ++ₗ suffix)
emitTopStmt-chars-head-not-newline _    (TVT vt)  suffix =
  emitValueTable-chars-head-not-newline vt suffix
emitTopStmt-chars-head-not-newline _    (TM  msg) suffix =
  emitMessage-chars-head-not-newline msg suffix
emitTopStmt-chars-head-not-newline _    (TEV ev)  suffix =
  emitEnvVar-chars-head-not-newline ev suffix
emitTopStmt-chars-head-not-newline _    (TCM cm)  suffix =
  emitComment-chars-head-not-newline cm suffix
emitTopStmt-chars-head-not-newline defs (TAT a)   suffix =
  -- β-prefix path: rewrite `emitAttribute-chars defs a` to its
  -- `'B' ∷ 'A' ∷ rest` head via the Σ-witness, then `∷-stop refl`
  -- because `isNewlineStart 'B' ≡ false`.
  subst (λ xs → SuffixStops isNewlineStart (xs ++ₗ suffix))
        (sym (proj₂ (emitAttribute-chars-BA-head defs a)))
        SS-BA
  where
    open import Aletheia.DBC.TextParser.DecRatParse.Properties using (∷-stop)
    SS-BA : SuffixStops isNewlineStart
              (('B' ∷ 'A' ∷ proj₁ (emitAttribute-chars-BA-head defs a))
               ++ₗ suffix)
    SS-BA = ∷-stop refl
emitTopStmt-chars-head-not-newline _    (TSG sg)  suffix =
  emitSignalGroup-chars-head-not-newline sg suffix
-- Phase E.5α: head of `emitValueDescription-chars rvd ++ suffix` is `'V'`,
-- not a newline-start.
emitTopStmt-chars-head-not-newline _    (TVD _)   _      = ∷-stop refl
  where open import Aletheia.DBC.TextParser.DecRatParse.Properties using (∷-stop)
