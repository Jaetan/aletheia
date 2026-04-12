{-# OPTIONS --safe --without-K #-}

-- JSON value extraction and typed lookup helpers.
--
-- Purpose: Extract typed values from JSON and look up fields in JSON objects.
-- All lookups return Maybe, propagating parse failures.
module Aletheia.Protocol.JSON.Lookup where

open import Data.String using (String)
open import Data.List using (List)
open import Data.Bool using (Bool)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (ℤ; +_; -[1+_]; ∣_∣)
open import Data.Rational as Rat using (ℚ; _/_; toℚᵘ)
open import Data.Rational.Unnormalised as ℚᵘ using (ℚᵘ; mkℚᵘ)
open import Data.Product using (_×_)
open import Data.Nat.Divisibility using (_∣?_)
open import Relation.Nullary using (yes; no)
open import Aletheia.Prelude using (lookupByKey)
open import Aletheia.Protocol.JSON.Types using (JSON; JNull; JBool; JNumber; JString; JArray; JObject)

-- ============================================================================
-- VALUE EXTRACTORS
-- ============================================================================

-- Get string value from JSON
getString : JSON → Maybe String
getString (JString s) = just s
getString _ = nothing

-- Get boolean value from JSON
getBool : JSON → Maybe Bool
getBool (JBool b) = just b
getBool _ = nothing

-- Get integer value from JSON (rational must be an integer)
-- Works by checking if numerator is divisible by denominator
-- NOTE: ℚᵘ stores denominator-1, so actual denominator = pattern + 1
getInt : JSON → Maybe ℤ
getInt (JNumber r) = checkInteger (Rat.toℚᵘ r)
  where
    -- Divide integer by suc n (automatically proves NonZero)
    divideInteger : ℤ → ℕ → ℤ
    divideInteger (+ m) zero = + m  -- Denominator is 1, return as-is
    divideInteger -[1+ m ] zero = -[1+ m ]  -- Denominator is 1, return as-is
    divideInteger (+ m) (suc n) = + (m Data.Nat./ (suc (suc n)))
    divideInteger -[1+ m ] (suc n) = -[1+ (m Data.Nat./ (suc (suc n))) ]

    checkInteger : ℚᵘ → Maybe ℤ
    checkInteger (ℚᵘ.mkℚᵘ num denom-1) with (suc denom-1) ∣? ∣ num ∣
    ... | yes _ = just (divideInteger num denom-1)
    ... | no _ = nothing
getInt _ = nothing

-- Extract natural number from JSON (rational must be positive integer)
getNat : JSON → Maybe ℕ
getNat (JNumber r) = extractNat (getInt (JNumber r))
  where
    extractNat : Maybe ℤ → Maybe ℕ
    extractNat (just (+ n)) = just n
    extractNat _ = nothing
getNat _ = nothing

-- Get rational value from JSON (supports both decimal and object formats)
-- Accepts: JNumber (direct rational) or {"numerator": n, "denominator": d}
getRational : JSON → Maybe ℚ
getRational (JNumber r) = just r
getRational (JObject fields) =
  lookupByKey "numerator" fields >>= λ numJSON →
  getInt numJSON >>= λ num →
  lookupByKey "denominator" fields >>= λ denomJSON →
  getNat denomJSON >>= λ where
    zero    → nothing
    (suc d) → just (num / suc d)
getRational _ = nothing

-- Get array value from JSON
getArray : JSON → Maybe (List JSON)
getArray (JArray xs) = just xs
getArray _ = nothing

-- Get object value from JSON
getObject : JSON → Maybe (List (String × JSON))
getObject (JObject fields) = just fields
getObject _ = nothing

-- ============================================================================
-- TYPED LOOKUP HELPERS
-- ============================================================================

-- Generic lookup combinator: lookup key, then extract with given function
private
  lookupWith : {A : Set} → (JSON → Maybe A) → String → List (String × JSON) → Maybe A
  lookupWith extract key obj with lookupByKey key obj
  ... | nothing = nothing
  ... | just v = extract v

lookupString : String → List (String × JSON) → Maybe String
lookupString = lookupWith getString

lookupBool : String → List (String × JSON) → Maybe Bool
lookupBool = lookupWith getBool

lookupInt : String → List (String × JSON) → Maybe ℤ
lookupInt = lookupWith getInt

lookupNat : String → List (String × JSON) → Maybe ℕ
lookupNat = lookupWith getNat

lookupRational : String → List (String × JSON) → Maybe ℚ
lookupRational = lookupWith getRational

lookupArray : String → List (String × JSON) → Maybe (List JSON)
lookupArray = lookupWith getArray

lookupObject : String → List (String × JSON) → Maybe (List (String × JSON))
lookupObject = lookupWith getObject
