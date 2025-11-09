{-# OPTIONS --safe --without-K #-}

module Aletheia.Parser.Properties where

open import Aletheia.Parser.Combinators
open import Data.List using (List)
open import Data.Char using (Char)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- TODO: Prove monad laws
-- TODO: Prove round-trip properties for specific parsers
