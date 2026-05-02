{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4c — `emit*-chars` `'B'∷'A'∷` prefix lemmas + generalized
-- `parseTopStmt-on-BA-head` accepting an arbitrary input + propositional
-- prefix witness.
--
-- The cost driver in the per-shape TAT TopStmt dispatcher is that
-- `emitAttrDef-chars` (top-level `with isRelScope`) and
-- `emitAttrAssign-chars` (target-dispatched `body` where-helper) do NOT
-- reduce to expose a `'B'∷'A'∷rest` head without case-splitting on the
-- scope/target.  The original 15-case dispatcher forced 7+7 such case-
-- splits inside a goal type that ALSO had to reduce
-- `liftTopStmt`/`advancePositions`/`mkResult` for each case, OOM-ing under
-- -M16G.
--
-- This module isolates the per-shape reduction work to a small `≡`-typed
-- lemma whose goal contains only `emit*-chars`.  The full TopStmt goal
-- (which contains the parseTopStmt/parseAttrLine/liftTopStmt chain)
-- becomes a single non-pattern-matching call site that consumes the
-- prefix lemma + a generalized BA-head lift.
module Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.PrefixHead where

open import Data.Char  using (Char)
open import Data.List  using (List; []; _∷_)
  renaming (_++_ to _++ₗ_)
open import Data.Maybe using (just)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Aletheia.Parser.Combinators using
  (Position; ParseResult; mkResult)

open import Aletheia.DBC.Types using
  ( AttrDef; mkAttrDef
  ; AttrScope
  ; ASNetwork; ASNode; ASMessage; ASSignal; ASEnvVar
  ; ASNodeMsg; ASNodeSig
  ; AttrAssign; mkAttrAssign
  ; AttrTarget
  ; ATgtNetwork; ATgtNode; ATgtMessage; ATgtSignal; ATgtEnvVar
  ; ATgtNodeMsg; ATgtNodeSig
  ; AttrDefault
  ; DBCAttribute; DBCAttrDef; DBCAttrDefault; DBCAttrAssign
  )

open import Aletheia.DBC.TextFormatter.Attributes using
  ( emitAttrDef-chars
  ; emitAttrDefault-chars
  ; emitAttrAssign-chars
  ; emitAttribute-chars
  )

open import Aletheia.DBC.TextParser.Attributes using
  (RawDBCAttribute; parseAttrLine)
open import Aletheia.DBC.TextParser.TopLevel using
  (TopStmt; TSAttribute; parseTopStmt)

open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute using
  (parseTopStmt-on-BA-head)

-- ============================================================================
-- PREFIX LEMMAS  (per emit-shape)
-- ============================================================================
--
-- Each lemma case-splits on the dispatching field (scope / target) and
-- returns the residual after the `'B'∷'A'∷` prefix.  Goal type is just
-- `≡` on `List Char`, so the elaborator only reduces `emit*-chars`, not
-- the surrounding TopStmt goal.

emitAttrDef-chars-BA-head :
    ∀ (d : AttrDef)
  → Σ[ rest ∈ List Char ] (emitAttrDef-chars d ≡ 'B' ∷ 'A' ∷ rest)
emitAttrDef-chars-BA-head (mkAttrDef _ ASNetwork _) = _ , refl
emitAttrDef-chars-BA-head (mkAttrDef _ ASNode    _) = _ , refl
emitAttrDef-chars-BA-head (mkAttrDef _ ASMessage _) = _ , refl
emitAttrDef-chars-BA-head (mkAttrDef _ ASSignal  _) = _ , refl
emitAttrDef-chars-BA-head (mkAttrDef _ ASEnvVar  _) = _ , refl
emitAttrDef-chars-BA-head (mkAttrDef _ ASNodeMsg _) = _ , refl
emitAttrDef-chars-BA-head (mkAttrDef _ ASNodeSig _) = _ , refl

emitAttrDefault-chars-BA-head :
    ∀ (defs : List AttrDef) (d : AttrDefault)
  → Σ[ rest ∈ List Char ] (emitAttrDefault-chars defs d ≡ 'B' ∷ 'A' ∷ rest)
emitAttrDefault-chars-BA-head defs d = _ , refl

emitAttrAssign-chars-BA-head :
    ∀ (a : AttrAssign)
  → Σ[ rest ∈ List Char ] (emitAttrAssign-chars a ≡ 'B' ∷ 'A' ∷ rest)
emitAttrAssign-chars-BA-head (mkAttrAssign _ ATgtNetwork       _) = _ , refl
emitAttrAssign-chars-BA-head (mkAttrAssign _ (ATgtNode _)      _) = _ , refl
emitAttrAssign-chars-BA-head (mkAttrAssign _ (ATgtMessage _)   _) = _ , refl
emitAttrAssign-chars-BA-head (mkAttrAssign _ (ATgtSignal _ _)  _) = _ , refl
emitAttrAssign-chars-BA-head (mkAttrAssign _ (ATgtEnvVar _)    _) = _ , refl
emitAttrAssign-chars-BA-head (mkAttrAssign _ (ATgtNodeMsg _ _) _) = _ , refl
emitAttrAssign-chars-BA-head (mkAttrAssign _ (ATgtNodeSig _ _ _) _) = _ , refl

emitAttribute-chars-BA-head :
    ∀ (defs : List AttrDef) (a : DBCAttribute)
  → Σ[ rest ∈ List Char ] (emitAttribute-chars defs a ≡ 'B' ∷ 'A' ∷ rest)
emitAttribute-chars-BA-head defs (DBCAttrDef d) =
  let (rest , eq) = emitAttrDef-chars-BA-head d in rest , eq
emitAttribute-chars-BA-head defs (DBCAttrDefault d) =
  let (rest , eq) = emitAttrDefault-chars-BA-head defs d in rest , eq
emitAttribute-chars-BA-head defs (DBCAttrAssign a) =
  let (rest , eq) = emitAttrAssign-chars-BA-head a in rest , eq

-- ============================================================================
-- GENERALIZED BA-HEAD LIFT  (input + propositional prefix witness)
-- ============================================================================

parseTopStmt-on-BA-head-via-prefix :
    ∀ (pos : Position) (input : List Char) (rest : List Char)
      (a : RawDBCAttribute) (outer : List Char) (pos-end : Position)
  → input ≡ 'B' ∷ 'A' ∷ rest
  → parseAttrLine pos input ≡ just (mkResult a pos-end outer)
  → parseTopStmt pos input ≡ just (mkResult (TSAttribute a) pos-end outer)
parseTopStmt-on-BA-head-via-prefix pos input rest a outer pos-end input-eq witness =
  subst (λ x → parseTopStmt pos x ≡ just (mkResult (TSAttribute a) pos-end outer))
        (sym input-eq)
        (parseTopStmt-on-BA-head pos a rest outer pos-end
          (subst (λ x → parseAttrLine pos x ≡ just (mkResult a pos-end outer))
                 input-eq
                 witness))
