{-# OPTIONS --safe --without-K #-}

-- JSON parser for LTL formulas with signal predicates.
--
-- Purpose: Parse LTL properties from JSON objects sent by Python client.
-- Handles: Temporal operators (always, eventually, next, until, and, or, not),
--          Signal predicates (equals, lessThan, greaterThan, between, changedBy).
-- Role: Protocol.Routing uses this to parse "setProperties" command payload.
--
-- Format: Nested JSON objects with "operator" and "predicate" fields.
-- Example: {"operator": "always", "formula": {"operator": "atomic", "predicate": {...}}}
module Aletheia.LTL.JSON where

open import Data.String using (String; _≟_)
open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Rational using (ℚ; _/_)
open import Data.Integer using (ℤ; +_)
open import Data.Nat using (ℕ; suc; zero; _≡ᵇ_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Aletheia.Prelude using (lookupByKey)
open import Aletheia.Protocol.JSON
open import Aletheia.LTL.Syntax using (LTL)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate)

-- ============================================================================
-- CONSTANTS
-- ============================================================================

-- Maximum nesting depth for LTL formula parsing
-- Prevents infinite recursion and stack overflow on malformed input
ltl-max-nesting-depth : ℕ
ltl-max-nesting-depth = 100

-- ============================================================================
-- SIGNAL PREDICATE PARSING - Factored into helper functions
-- ============================================================================
-- Note: lookupRational is now provided by Aletheia.Protocol.JSON

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

-- Parse LessThanOrEqual predicate
parseLessThanOrEqual : List (String × JSON) → Maybe SignalPredicate
parseLessThanOrEqual obj = do
  signal ← lookupString "signal" obj
  value ← lookupRational "value" obj
  just (SignalPredicate.LessThanOrEqual signal value)

-- Parse GreaterThanOrEqual predicate
parseGreaterThanOrEqual : List (String × JSON) → Maybe SignalPredicate
parseGreaterThanOrEqual obj = do
  signal ← lookupString "signal" obj
  value ← lookupRational "value" obj
  just (SignalPredicate.GreaterThanOrEqual signal value)

-- Parse ChangedBy predicate
parseChangedBy : List (String × JSON) → Maybe SignalPredicate
parseChangedBy obj = do
  signal ← lookupString "signal" obj
  delta ← lookupRational "delta" obj
  just (SignalPredicate.ChangedBy signal delta)

-- Dispatch table for signal predicates
predicateDispatchTable : List (String × (List (String × JSON) → Maybe SignalPredicate))
predicateDispatchTable =
  ("equals" , parseEquals) ∷
  ("lessThan" , parseLessThan) ∷
  ("greaterThan" , parseGreaterThan) ∷
  ("lessThanOrEqual" , parseLessThanOrEqual) ∷
  ("greaterThanOrEqual" , parseGreaterThanOrEqual) ∷
  ("between" , parseBetween) ∷
  ("changedBy" , parseChangedBy) ∷
  []

-- Helper: Dispatch to correct predicate parser based on type (using dispatch table)
dispatchPredicate : String → List (String × JSON) → Maybe SignalPredicate
dispatchPredicate predType obj with lookupByKey predType predicateDispatchTable
... | nothing = nothing  -- Unknown predicate type
... | just parser = parser obj

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
parseNever : ℕ → List (String × JSON) → Maybe (LTL SignalPredicate)
parseImplies : ℕ → List (String × JSON) → Maybe (LTL SignalPredicate)
parseLTLObject : ℕ → List (String × JSON) → Maybe (LTL SignalPredicate)

-- Parse atomic predicate (refactored to avoid nested with clauses)
parseAtomic depth obj = do
  predObj ← lookupObject "predicate" obj
  pred ← parseSignalPredicate predObj
  just (LTL.Atomic pred)

-- Parse unary operator (Not, Next, Always, Eventually)
parseUnary zero ctor obj = nothing
parseUnary (suc depth) ctor obj = do
  formulaJSON ← lookupByKey "formula" obj
  formula ← parseLTL depth formulaJSON
  just (ctor formula)

-- Parse binary operator (And, Or, Until)
parseBinary zero ctor obj = nothing
parseBinary (suc depth) ctor obj = do
  leftJSON ← lookupByKey "left" obj
  rightJSON ← lookupByKey "right" obj
  left ← parseLTL depth leftJSON
  right ← parseLTL depth rightJSON
  just (ctor left right)

-- Parse bounded operator (MetricEventually, MetricAlways)
parseBounded zero ctor obj = nothing
parseBounded (suc depth) ctor obj = do
  timebound ← lookupNat "timebound" obj
  formulaJSON ← lookupByKey "formula" obj
  formula ← parseLTL depth formulaJSON
  just (ctor timebound formula)

-- Parse "never" as Always(Not(formula))
parseNever zero obj = nothing
parseNever (suc depth) obj = do
  formulaJSON ← lookupByKey "formula" obj
  formula ← parseLTL depth formulaJSON
  just (LTL.Always (LTL.Not formula))

-- Parse "implies" as Or(Not(antecedent), consequent)
parseImplies zero obj = nothing
parseImplies (suc depth) obj = do
  antJSON ← lookupByKey "antecedent" obj
  consJSON ← lookupByKey "consequent" obj
  ant ← parseLTL depth antJSON
  cons ← parseLTL depth consJSON
  just (LTL.Or (LTL.Not ant) cons)

-- Parse bounded binary operator (MetricUntil, MetricRelease)
parseBoundedBinary : ℕ → (ℕ → LTL SignalPredicate → LTL SignalPredicate → LTL SignalPredicate) → List (String × JSON) → Maybe (LTL SignalPredicate)
parseBoundedBinary zero ctor obj = nothing
parseBoundedBinary (suc depth) ctor obj = do
  timebound ← lookupNat "timebound" obj
  leftJSON ← lookupByKey "left" obj
  rightJSON ← lookupByKey "right" obj
  left ← parseLTL depth leftJSON
  right ← parseLTL depth rightJSON
  just (ctor timebound left right)

-- Helper: Dispatch to correct operator parser based on type
-- Note: Using if-then-else instead of dispatch table to maintain termination checking
-- (dispatch tables hide structural recursion from Agda's termination checker)
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
  else if ⌊ op ≟ "release" ⌋ then parseBinary depth LTL.Release obj
  else if ⌊ op ≟ "metricEventually" ⌋ then parseBounded depth LTL.MetricEventually obj
  else if ⌊ op ≟ "metricAlways" ⌋ then parseBounded depth LTL.MetricAlways obj
  else if ⌊ op ≟ "metricUntil" ⌋ then parseBoundedBinary depth LTL.MetricUntil obj
  else if ⌊ op ≟ "metricRelease" ⌋ then parseBoundedBinary depth LTL.MetricRelease obj
  else if ⌊ op ≟ "never" ⌋ then parseNever depth obj
  else if ⌊ op ≟ "implies" ⌋ then parseImplies depth obj
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
parseProperty = parseLTL ltl-max-nesting-depth
