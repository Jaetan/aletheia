{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4c — TAT (TSAttribute) dispatcher under head-dispatched
-- parseTopStmt.
--
-- Every attribute-line emitter starts with `toList "BA_..."` which
-- definitionally reduces to `'B' ∷ 'A' ∷ '_' ∷ …`.  parseTopStmt's
-- head dispatch matches that BA-bucket: `parseAttrLine >>= λ a → pure
-- (TSAttribute a)`.
--
-- One generic helper `parseTopStmt-on-BA-head` lifts ANY parseAttrLine
-- success (from the 31 `parseAttrLine-roundtrip-*` lemmas in
-- `Properties/Attributes/Line.agda`) to a parseTopStmt success.  Per-
-- shape dispatchers compose in the universal aggregator without
-- requiring 31 separate lift wrappers.
module Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute where

open import Data.Char  using (Char)
open import Data.List  using (List; _∷_)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality
  using (_≡_)

open import Aletheia.Parser.Combinators using
  (Position; ParseResult; mkResult;
   _>>=_; pure)

open import Aletheia.DBC.TextParser.TopLevel using
  (TopStmt; TSAttribute; parseTopStmt)
open import Aletheia.DBC.TextParser.Attributes using
  (RawDBCAttribute; parseAttrLine)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (bind-just-step)

-- Lift any parseAttrLine success on a 'B'∷'A'∷rest input into a
-- parseTopStmt success at the same position/result/suffix.  The pattern
-- match in parseTopStmt fires on the literal head, reducing the goal to
-- the BA-bucket `parseAttrLine >>= λ a → pure (TSAttribute a)`; then
-- bind-just-step closes via the input witness.
parseTopStmt-on-BA-head :
    ∀ (pos : Position) (a : RawDBCAttribute) (rest : List Char)
      (outer : List Char) (pos-end : Position)
  → parseAttrLine pos ('B' ∷ 'A' ∷ rest)
    ≡ just (mkResult a pos-end outer)
  → parseTopStmt pos ('B' ∷ 'A' ∷ rest)
    ≡ just (mkResult (TSAttribute a) pos-end outer)
parseTopStmt-on-BA-head pos a rest outer pos-end wit =
  bind-just-step parseAttrLine (λ a → pure (TSAttribute a))
    pos ('B' ∷ 'A' ∷ rest) a pos-end outer wit
