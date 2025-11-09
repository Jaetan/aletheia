{-# OPTIONS --safe --without-K #-}

module Aletheia.LTL.Semantics where

open import Aletheia.LTL.Syntax
open import Aletheia.Trace.Stream
open import Data.Bool using (Bool)

_⊨_ : ∀ {A : Set} → Trace A → LTL (A → Bool) → Bool
trace ⊨ formula = {!!}
