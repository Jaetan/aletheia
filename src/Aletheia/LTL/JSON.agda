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
--
-- Recursion: Structurally recursive on JSON input.
-- Each sub-formula is extracted via lookupAndParse, which walks the JSON field
-- list and calls parseLTL on the structurally smaller sub-value.
module Aletheia.LTL.JSON where

open import Data.String using (String; _≟_)
open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Aletheia.Prelude using (lookupByKey)
open import Aletheia.JSON using (JSON; JObject; lookupString; lookupRational; lookupObject; lookupNat)
open import Aletheia.LTL.Syntax using (LTL)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate; ValueP; DeltaP)
import Aletheia.LTL.SignalPredicate as SP

-- ============================================================================
-- SIGNAL PREDICATE PARSING (internal helpers)
-- ============================================================================

private
  parseEquals : List (String × JSON) → Maybe SignalPredicate
  parseEquals obj = do
    signal ← lookupString "signal" obj
    value ← lookupRational "value" obj
    just (ValueP (SP.Equals signal value))

  parseLessThan : List (String × JSON) → Maybe SignalPredicate
  parseLessThan obj = do
    signal ← lookupString "signal" obj
    value ← lookupRational "value" obj
    just (ValueP (SP.LessThan signal value))

  parseGreaterThan : List (String × JSON) → Maybe SignalPredicate
  parseGreaterThan obj = do
    signal ← lookupString "signal" obj
    value ← lookupRational "value" obj
    just (ValueP (SP.GreaterThan signal value))

  parseBetween : List (String × JSON) → Maybe SignalPredicate
  parseBetween obj = do
    signal ← lookupString "signal" obj
    minVal ← lookupRational "min" obj
    maxVal ← lookupRational "max" obj
    just (ValueP (SP.Between signal minVal maxVal))

  parseLessThanOrEqual : List (String × JSON) → Maybe SignalPredicate
  parseLessThanOrEqual obj = do
    signal ← lookupString "signal" obj
    value ← lookupRational "value" obj
    just (ValueP (SP.LessThanOrEqual signal value))

  parseGreaterThanOrEqual : List (String × JSON) → Maybe SignalPredicate
  parseGreaterThanOrEqual obj = do
    signal ← lookupString "signal" obj
    value ← lookupRational "value" obj
    just (ValueP (SP.GreaterThanOrEqual signal value))

  parseChangedBy : List (String × JSON) → Maybe SignalPredicate
  parseChangedBy obj = do
    signal ← lookupString "signal" obj
    delta ← lookupRational "delta" obj
    just (DeltaP (SP.ChangedBy signal delta))

  parseStableWithin : List (String × JSON) → Maybe SignalPredicate
  parseStableWithin obj = do
    signal ← lookupString "signal" obj
    tolerance ← lookupRational "tolerance" obj
    just (DeltaP (SP.StableWithin signal tolerance))

  predicateDispatchTable : List (String × (List (String × JSON) → Maybe SignalPredicate))
  predicateDispatchTable =
    ("equals" , parseEquals) ∷
    ("lessThan" , parseLessThan) ∷
    ("greaterThan" , parseGreaterThan) ∷
    ("lessThanOrEqual" , parseLessThanOrEqual) ∷
    ("greaterThanOrEqual" , parseGreaterThanOrEqual) ∷
    ("between" , parseBetween) ∷
    ("changedBy" , parseChangedBy) ∷
    ("stableWithin" , parseStableWithin) ∷
    []

  dispatchPredicate : String → List (String × JSON) → Maybe SignalPredicate
  dispatchPredicate predType obj with lookupByKey predType predicateDispatchTable
  ... | nothing = nothing
  ... | just parser = parser obj

-- Parse a signal predicate from JSON object fields
parseSignalPredicate : List (String × JSON) → Maybe SignalPredicate
parseSignalPredicate obj = do
  predType ← lookupString "predicate" obj
  dispatchPredicate predType obj

-- ============================================================================
-- LTL FORMULA PARSING - Structurally recursive on JSON input
-- ============================================================================

mutual
  -- Parse an LTL formula from JSON.
  -- Structurally recursive: sub-formulas are extracted from JSON object fields,
  -- which are strictly smaller than the enclosing JObject constructor.
  parseLTL : JSON → Maybe (LTL SignalPredicate)
  parseLTL (JObject obj) = do
    op ← lookupString "operator" obj
    dispatchOperator op obj
  parseLTL _ = nothing

  -- Walk the field list to find a key, then recursively parse its JSON value.
  -- This makes the structural decrease visible to Agda's termination checker:
  -- the value v in (k , v) ∷ rest is a sub-component of the enclosing JObject.
  lookupAndParse : String → List (String × JSON) → Maybe (LTL SignalPredicate)
  lookupAndParse key [] = nothing
  lookupAndParse key ((k , v) ∷ rest) =
    if ⌊ key ≟ k ⌋ then parseLTL v
    else lookupAndParse key rest

  -- Dispatch to correct operator parser.
  -- Cold path: runs once per JSON property definition (not per frame).
  -- Uses if-then-else (not a dispatch table) so Agda's termination checker
  -- can see through to the recursive calls.
  dispatchOperator : String → List (String × JSON) → Maybe (LTL SignalPredicate)
  dispatchOperator op obj =
    if ⌊ op ≟ "atomic" ⌋ then parseAtomicOp obj
    else if ⌊ op ≟ "not" ⌋ then parseUnaryOp LTL.Not obj
    else if ⌊ op ≟ "and" ⌋ then parseBinaryOp LTL.And obj
    else if ⌊ op ≟ "or" ⌋ then parseBinaryOp LTL.Or obj
    else if ⌊ op ≟ "next" ⌋ then parseUnaryOp LTL.Next obj
    else if ⌊ op ≟ "weakNext" ⌋ then parseUnaryOp LTL.WNext obj
    else if ⌊ op ≟ "always" ⌋ then parseUnaryOp LTL.Always obj
    else if ⌊ op ≟ "eventually" ⌋ then parseUnaryOp LTL.Eventually obj
    else if ⌊ op ≟ "until" ⌋ then parseBinaryOp LTL.Until obj
    else if ⌊ op ≟ "release" ⌋ then parseBinaryOp LTL.Release obj
    -- Metric operators: startTime initialized to 0 (= uninitialized, suc-encoded).
    -- timebound=0 is accepted: means "must hold immediately" (see Syntax.agda).
    else if ⌊ op ≟ "metricEventually" ⌋ then parseBoundedOp (λ n → LTL.MetricEventually n 0) obj
    else if ⌊ op ≟ "metricAlways" ⌋ then parseBoundedOp (λ n → LTL.MetricAlways n 0) obj
    else if ⌊ op ≟ "metricUntil" ⌋ then parseBoundedBinaryOp (λ n → LTL.MetricUntil n 0) obj
    else if ⌊ op ≟ "metricRelease" ⌋ then parseBoundedBinaryOp (λ n → LTL.MetricRelease n 0) obj
    else if ⌊ op ≟ "never" ⌋ then parseNeverOp obj
    else if ⌊ op ≟ "implies" ⌋ then parseImpliesOp obj
    else nothing

  -- Parse atomic predicate (no recursive LTL parsing)
  parseAtomicOp : List (String × JSON) → Maybe (LTL SignalPredicate)
  parseAtomicOp obj = do
    predObj ← lookupObject "predicate" obj
    pred ← parseSignalPredicate predObj
    just (LTL.Atomic pred)

  -- Parse unary operator (Not, Next, Always, Eventually)
  parseUnaryOp : (LTL SignalPredicate → LTL SignalPredicate)
               → List (String × JSON) → Maybe (LTL SignalPredicate)
  parseUnaryOp ctor obj = do
    formula ← lookupAndParse "formula" obj
    just (ctor formula)

  -- Parse binary operator (And, Or, Until, Release)
  parseBinaryOp : (LTL SignalPredicate → LTL SignalPredicate → LTL SignalPredicate)
                → List (String × JSON) → Maybe (LTL SignalPredicate)
  parseBinaryOp ctor obj = do
    left ← lookupAndParse "left" obj
    right ← lookupAndParse "right" obj
    just (ctor left right)

  -- Parse bounded unary operator (MetricEventually, MetricAlways)
  parseBoundedOp : (ℕ → LTL SignalPredicate → LTL SignalPredicate)
                 → List (String × JSON) → Maybe (LTL SignalPredicate)
  parseBoundedOp ctor obj = do
    timebound ← lookupNat "timebound" obj
    formula ← lookupAndParse "formula" obj
    just (ctor timebound formula)

  -- Parse bounded binary operator (MetricUntil, MetricRelease)
  parseBoundedBinaryOp : (ℕ → LTL SignalPredicate → LTL SignalPredicate → LTL SignalPredicate)
                       → List (String × JSON) → Maybe (LTL SignalPredicate)
  parseBoundedBinaryOp ctor obj = do
    timebound ← lookupNat "timebound" obj
    left ← lookupAndParse "left" obj
    right ← lookupAndParse "right" obj
    just (ctor timebound left right)

  -- Parse "never" as Always(Not(formula))
  parseNeverOp : List (String × JSON) → Maybe (LTL SignalPredicate)
  parseNeverOp obj = do
    formula ← lookupAndParse "formula" obj
    just (LTL.Always (LTL.Not formula))

  -- Parse "implies" as Or(Not(antecedent), consequent)
  parseImpliesOp : List (String × JSON) → Maybe (LTL SignalPredicate)
  parseImpliesOp obj = do
    ant ← lookupAndParse "antecedent" obj
    cons ← lookupAndParse "consequent" obj
    just (LTL.Or (LTL.Not ant) cons)

-- ============================================================================
-- PUBLIC API
-- ============================================================================

parseProperty : JSON → Maybe (LTL SignalPredicate)
parseProperty = parseLTL
