{-# OPTIONS --safe --without-K #-}

-- JSON data type definition.
--
-- Purpose: Core JSON value representation used throughout the protocol layer.
-- Numbers use rationals (ℚ) for exact decimal representation.
module Aletheia.Protocol.JSON.Types where

open import Data.String using (String)
open import Data.List using (List)
open import Data.Bool using (Bool)
open import Data.Rational using (ℚ)
open import Data.Product using (_×_)

-- JSON value representation
-- Numbers are represented as rationals (ℚ) to support decimal values
data JSON : Set where
  JNull   : JSON
  JBool   : Bool → JSON
  JNumber : ℚ → JSON
  JString : String → JSON
  JArray  : List JSON → JSON
  JObject : List (String × JSON) → JSON
