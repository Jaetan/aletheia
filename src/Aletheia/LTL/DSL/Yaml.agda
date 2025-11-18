{-# OPTIONS --safe --without-K #-}

module Aletheia.LTL.DSL.Yaml where

open import Data.List using (List; []; _∷_)
open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ)
open import Data.Rational using (ℚ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)

-- ============================================================================
-- YAML INTERMEDIATE REPRESENTATION
-- ============================================================================

-- Simple tree structure representing parsed YAML
-- This separates parsing (phase 1) from AST construction (phase 2)
data YamlValue : Set where
  -- Primitive values
  YString : String → YamlValue
  YNat : ℕ → YamlValue
  YRational : ℚ → YamlValue

  -- Structured values
  YObject : List (String × YamlValue) → YamlValue

-- Helper: Lookup a field in a YAML object
lookupField : String → YamlValue → Maybe YamlValue
lookupField key (YObject fields) = lookup key fields
  where
    lookup : String → List (String × YamlValue) → Maybe YamlValue
    lookup _ [] = nothing
    lookup k (pair ∷ rest) with k ≟ proj₁ pair
    ... | yes _ = just (proj₂ pair)
    ... | no _ = lookup k rest
lookupField _ _ = nothing

-- Helper: Extract string from YamlValue
asString : YamlValue → Maybe String
asString (YString s) = just s
asString _ = nothing

-- Helper: Extract nat from YamlValue
asNat : YamlValue → Maybe ℕ
asNat (YNat n) = just n
asNat _ = nothing

-- Helper: Extract rational from YamlValue
asRational : YamlValue → Maybe ℚ
asRational (YRational q) = just q
asRational _ = nothing
