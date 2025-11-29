{-# OPTIONS --safe --without-K --guardedness #-}

module Aletheia.LTL.JSON where

open import Data.String using (String; _≟_)
open import Data.Bool using (if_then_else_)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Rational using (ℚ; _/_)
open import Data.Integer using (ℤ; +_)
open import Data.Nat using (ℕ; suc; zero; _≡ᵇ_)
open import Data.Product using (_×_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Aletheia.Protocol.JSON
open import Aletheia.LTL.Syntax using (LTL)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate)

-- ============================================================================
-- RATIONAL LOOKUP (JSON numbers are now rationals directly)
-- ============================================================================

-- Lookup and extract rational in one step
lookupRational : String → List (String × JSON) → Maybe ℚ
lookupRational key obj with lookup key obj
... | nothing = nothing
... | just v = getRational v

-- ============================================================================
-- SIGNAL PREDICATE PARSING - Factored into helper functions
-- ============================================================================

-- Parse Equals predicate
parseEquals : List (String × JSON) → Maybe SignalPredicate
parseEquals obj = do
  signal ← lookupString "signal" obj
  value ← lookupRational "value" obj
  just (SignalPredicate.Equals signal value)

-- Parse LessThan predicate
parseLessThan : List (String × JSON) → Maybe SignalPredicate
parseLessThan obj = do
  signal ← lookupString "signal" obj
  value ← lookupRational "value" obj
  just (SignalPredicate.LessThan signal value)

-- Parse GreaterThan predicate
parseGreaterThan : List (String × JSON) → Maybe SignalPredicate
parseGreaterThan obj = do
  signal ← lookupString "signal" obj
  value ← lookupRational "value" obj
  just (SignalPredicate.GreaterThan signal value)

-- Parse Between predicate
parseBetween : List (String × JSON) → Maybe SignalPredicate
parseBetween obj = do
  signal ← lookupString "signal" obj
  minVal ← lookupRational "min" obj
  maxVal ← lookupRational "max" obj
  just (SignalPredicate.Between signal minVal maxVal)

-- Parse ChangedBy predicate
parseChangedBy : List (String × JSON) → Maybe SignalPredicate
parseChangedBy obj = do
  signal ← lookupString "signal" obj
  delta ← lookupRational "delta" obj
  just (SignalPredicate.ChangedBy signal delta)

-- Helper: Dispatch to correct predicate parser based on type
dispatchPredicate : String → List (String × JSON) → Maybe SignalPredicate
dispatchPredicate predType obj =
  if ⌊ predType ≟ "equals" ⌋ then parseEquals obj
  else if ⌊ predType ≟ "lessThan" ⌋ then parseLessThan obj
  else if ⌊ predType ≟ "greaterThan" ⌋ then parseGreaterThan obj
  else if ⌊ predType ≟ "between" ⌋ then parseBetween obj
  else if ⌊ predType ≟ "changedBy" ⌋ then parseChangedBy obj
  else nothing  -- Unknown predicate type

-- Dispatch table for signal predicates (refactored to avoid with clauses)
parseSignalPredicate : List (String × JSON) → Maybe SignalPredicate
parseSignalPredicate obj = do
  predType ← lookupString "predicate" obj
  dispatchPredicate predType obj

-- ============================================================================
-- LTL FORMULA PARSING - Clean dispatch pattern with depth measure
-- ============================================================================

-- Forward declarations for mutual recursion
parseLTL : ℕ → JSON → Maybe (LTL SignalPredicate)
parseAtomic : ℕ → List (String × JSON) → Maybe (LTL SignalPredicate)
parseUnary : ℕ → (LTL SignalPredicate → LTL SignalPredicate)
           → List (String × JSON) → Maybe (LTL SignalPredicate)
parseBinary : ℕ → (LTL SignalPredicate → LTL SignalPredicate → LTL SignalPredicate)
            → List (String × JSON) → Maybe (LTL SignalPredicate)
parseBounded : ℕ → (ℕ → LTL SignalPredicate → LTL SignalPredicate)
             → List (String × JSON) → Maybe (LTL SignalPredicate)
parseLTLObject : ℕ → List (String × JSON) → Maybe (LTL SignalPredicate)

-- Parse atomic predicate (refactored to avoid nested with clauses)
parseAtomic depth obj = do
  predObj ← lookupObject "predicate" obj
  pred ← parseSignalPredicate predObj
  just (LTL.Atomic pred)

-- Parse unary operator (Not, Next, Always, Eventually)
parseUnary zero ctor obj = nothing
parseUnary (suc depth) ctor obj = do
  formulaJSON ← lookup "formula" obj
  formula ← parseLTL depth formulaJSON
  just (ctor formula)

-- Parse binary operator (And, Or, Until)
parseBinary zero ctor obj = nothing
parseBinary (suc depth) ctor obj = do
  leftJSON ← lookup "left" obj
  rightJSON ← lookup "right" obj
  left ← parseLTL depth leftJSON
  right ← parseLTL depth rightJSON
  just (ctor left right)

-- Parse bounded operator (EventuallyWithin, AlwaysWithin)
parseBounded zero ctor obj = nothing
parseBounded (suc depth) ctor obj = do
  timebound ← lookupNat "timebound" obj
  formulaJSON ← lookup "formula" obj
  formula ← parseLTL depth formulaJSON
  just (ctor timebound formula)

-- Helper: Dispatch to correct operator parser based on type
dispatchOperator : String → ℕ → List (String × JSON) → Maybe (LTL SignalPredicate)
dispatchOperator op depth obj =
  if ⌊ op ≟ "atomic" ⌋ then parseAtomic depth obj
  else if ⌊ op ≟ "not" ⌋ then parseUnary depth LTL.Not obj
  else if ⌊ op ≟ "and" ⌋ then parseBinary depth LTL.And obj
  else if ⌊ op ≟ "or" ⌋ then parseBinary depth LTL.Or obj
  else if ⌊ op ≟ "next" ⌋ then parseUnary depth LTL.Next obj
  else if ⌊ op ≟ "always" ⌋ then parseUnary depth LTL.Always obj
  else if ⌊ op ≟ "eventually" ⌋ then parseUnary depth LTL.Eventually obj
  else if ⌊ op ≟ "until" ⌋ then parseBinary depth LTL.Until obj
  else if ⌊ op ≟ "eventuallyWithin" ⌋ then parseBounded depth LTL.EventuallyWithin obj
  else if ⌊ op ≟ "alwaysWithin" ⌋ then parseBounded depth LTL.AlwaysWithin obj
  else nothing  -- Unknown operator

-- Helper to avoid pattern matching issues
parseLTLObjectHelper : ℕ → List (String × JSON) → Maybe (LTL SignalPredicate)
parseLTLObjectHelper depth obj = do
  op ← lookupString "operator" obj
  dispatchOperator op depth obj

-- Dispatch table for LTL operators (keep structural recursion for termination)
parseLTLObject zero _ = nothing
parseLTLObject (suc depth) obj = parseLTLObjectHelper depth obj

-- Main parser helper to handle JSON type dispatch
parseLTLDispatch : ℕ → JSON → Maybe (LTL SignalPredicate)
parseLTLDispatch depth (JObject obj) = parseLTLObject depth obj
parseLTLDispatch _ _ = nothing

-- Main parser
parseLTL zero _ = nothing
parseLTL (suc depth) json = parseLTLDispatch depth json

-- ============================================================================
-- PUBLIC API
-- ============================================================================

parseProperty : JSON → Maybe (LTL SignalPredicate)
parseProperty = parseLTL 100  -- Max nesting depth of 100 (reasonable for LTL formulas)
