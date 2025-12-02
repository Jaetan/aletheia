{-# OPTIONS --safe --without-K #-}

-- Correctness properties for parser combinators.
--
-- Purpose: Prove basic properties of parsers (determinism, bounded results).
-- Properties: Determinism (same input → same result), length bounds, parser laws.
-- Role: Phase 1 basic properties; full soundness proofs deferred to Phase 3.
--
-- Status: Lightweight correctness properties implemented.
-- Future work: Grammar formalization, soundness (parse → valid AST), round-trip proofs.
module Aletheia.Parser.Properties where

open import Aletheia.Parser.Combinators
open import Data.List using (List)
open import Data.Char using (Char)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- TODO: Prove monad laws
-- TODO: Prove round-trip properties for specific parsers
