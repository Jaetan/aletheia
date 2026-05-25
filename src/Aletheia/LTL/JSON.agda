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
--
-- Failure surface (AGDA-D-10.1): the parser is reason-carrying — it returns
-- `ParseFail ⊎ _`, never a bare `Maybe`.  Signal-name validity is decided in
-- exactly ONE place (`Identifier.parseIdentifierField`, surfaced here through
-- `signalField`); an invalid name propagates up the single parse path as
-- `BadSignal <IdentifierError>`, and the handler renames the verdict to the
-- wire error.  There is no second validity walk to keep in sync.
module Aletheia.LTL.JSON where

open import Data.String using (String; _≟_)
open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₁)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Aletheia.Prelude using (lookupByKey)
open import Aletheia.JSON using (JSON; JObject; lookupString; lookupChars; lookupRational; lookupObject; lookupNat)
open import Aletheia.LTL.Syntax using (LTL)
open import Aletheia.Trace.Time using (mkTs)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate; ValueP; DeltaP)
import Aletheia.LTL.SignalPredicate as SP
open import Aletheia.DBC.Identifier using (Identifier; IdentifierError; parseIdentifierField)

-- ============================================================================
-- PARSE FAILURE — the single reason-carrying result type
-- ============================================================================
--
-- `Shape` — malformed JSON shape (missing key, unknown operator/predicate
--   discriminator, ill-typed sub-field).  Carries no payload; the handler
--   attaches the property index and emits `HandlerErr (PropertyParseFailed …)`.
-- `BadSignal e` — the `"signal"` value failed `parseIdentifierField`; `e`
--   classifies it (`TooLong`/`BadChars`).  The handler maps it to the typed
--   wire error (`InputBoundExceeded IdentifierLength` / `ParseErr
--   (InvalidIdentifier …)`).
data ParseFail : Set where
  Shape     : ParseFail
  BadSignal : IdentifierError → ParseFail

-- ============================================================================
-- SIGNAL PREDICATE PARSING (internal helpers)
-- ============================================================================

private
  -- Error-monad bind for `ParseFail ⊎ _` (short-circuits on `inj₁`).  This is
  -- the `_>>=_` the `do`-blocks below desugar against (the Maybe one is not in
  -- scope), so the typed failure threads through every parser uniformly.
  _>>=_ : ∀ {A B : Set} → ParseFail ⊎ A → (A → ParseFail ⊎ B) → ParseFail ⊎ B
  inj₁ e >>= _ = inj₁ e
  inj₂ a >>= f = f a

  -- Lift a shape lookup (`lookupX : … → Maybe A`) into the error monad: a
  -- missing/ill-typed field is a `Shape` failure.
  shape : ∀ {A : Set} → Maybe A → ParseFail ⊎ A
  shape = maybe inj₂ (inj₁ Shape)

  -- THE signal-name parse point: look up `"signal"` and run the single
  -- identifier decision, lifting its typed reason into `BadSignal`.  Every
  -- predicate parser routes its signal name through here.
  signalField : List (String × JSON) → ParseFail ⊎ Identifier
  signalField obj = do
    sigChars ← shape (lookupChars "signal" obj)
    map₁ BadSignal (parseIdentifierField sigChars)

  parseEquals : List (String × JSON) → ParseFail ⊎ SignalPredicate
  parseEquals obj = do
    signal ← signalField obj
    value ← shape (lookupRational "value" obj)
    inj₂ (ValueP (SP.Equals signal value))

  parseLessThan : List (String × JSON) → ParseFail ⊎ SignalPredicate
  parseLessThan obj = do
    signal ← signalField obj
    value ← shape (lookupRational "value" obj)
    inj₂ (ValueP (SP.LessThan signal value))

  parseGreaterThan : List (String × JSON) → ParseFail ⊎ SignalPredicate
  parseGreaterThan obj = do
    signal ← signalField obj
    value ← shape (lookupRational "value" obj)
    inj₂ (ValueP (SP.GreaterThan signal value))

  parseBetween : List (String × JSON) → ParseFail ⊎ SignalPredicate
  parseBetween obj = do
    signal ← signalField obj
    minVal ← shape (lookupRational "min" obj)
    maxVal ← shape (lookupRational "max" obj)
    inj₂ (ValueP (SP.Between signal minVal maxVal))

  parseLessThanOrEqual : List (String × JSON) → ParseFail ⊎ SignalPredicate
  parseLessThanOrEqual obj = do
    signal ← signalField obj
    value ← shape (lookupRational "value" obj)
    inj₂ (ValueP (SP.LessThanOrEqual signal value))

  parseGreaterThanOrEqual : List (String × JSON) → ParseFail ⊎ SignalPredicate
  parseGreaterThanOrEqual obj = do
    signal ← signalField obj
    value ← shape (lookupRational "value" obj)
    inj₂ (ValueP (SP.GreaterThanOrEqual signal value))

  parseChangedBy : List (String × JSON) → ParseFail ⊎ SignalPredicate
  parseChangedBy obj = do
    signal ← signalField obj
    delta ← shape (lookupRational "delta" obj)
    inj₂ (DeltaP (SP.ChangedBy signal delta))

  parseStableWithin : List (String × JSON) → ParseFail ⊎ SignalPredicate
  parseStableWithin obj = do
    signal ← signalField obj
    tolerance ← shape (lookupRational "tolerance" obj)
    inj₂ (DeltaP (SP.StableWithin signal tolerance))

  predicateDispatchTable : List (String × (List (String × JSON) → ParseFail ⊎ SignalPredicate))
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

  dispatchPredicate : String → List (String × JSON) → ParseFail ⊎ SignalPredicate
  dispatchPredicate predType obj with lookupByKey predType predicateDispatchTable
  ... | nothing = inj₁ Shape
  ... | just parser = parser obj

-- Parse a signal predicate from JSON object fields
parseSignalPredicate : List (String × JSON) → ParseFail ⊎ SignalPredicate
parseSignalPredicate obj = do
  predType ← shape (lookupString "predicate" obj)
  dispatchPredicate predType obj

-- ============================================================================
-- LTL FORMULA PARSING - Structurally recursive on JSON input
-- ============================================================================

mutual
  -- Parse an LTL formula from JSON.
  -- Structurally recursive: sub-formulas are extracted from JSON object fields,
  -- which are strictly smaller than the enclosing JObject constructor.
  parseLTL : JSON → ParseFail ⊎ (LTL SignalPredicate)
  parseLTL (JObject obj) = do
    op ← shape (lookupString "operator" obj)
    dispatchOperator op obj
  parseLTL _ = inj₁ Shape

  -- Walk the field list to find a key, then recursively parse its JSON value.
  -- This makes the structural decrease visible to Agda's termination checker:
  -- the value v in (k , v) ∷ rest is a sub-component of the enclosing JObject.
  lookupAndParse : String → List (String × JSON) → ParseFail ⊎ (LTL SignalPredicate)
  lookupAndParse key [] = inj₁ Shape
  lookupAndParse key ((k , v) ∷ rest) =
    if ⌊ key ≟ k ⌋ then parseLTL v
    else lookupAndParse key rest

  -- Dispatch to correct operator parser.
  -- Cold path: runs once per JSON property definition (not per frame).
  -- Uses if-then-else (not a dispatch table) so Agda's termination checker
  -- can see through to the recursive calls.
  dispatchOperator : String → List (String × JSON) → ParseFail ⊎ (LTL SignalPredicate)
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
    -- R6-B7.2 closure: lift JSON ℕ → `Timestamp μs` via `mkTs` at the parse
    -- boundary so the dimensional invariant holds inside the kernel.
    else if ⌊ op ≟ "metricEventually" ⌋ then parseBoundedOp (λ n → LTL.MetricEventually (mkTs n) 0) obj
    else if ⌊ op ≟ "metricAlways" ⌋ then parseBoundedOp (λ n → LTL.MetricAlways (mkTs n) 0) obj
    else if ⌊ op ≟ "metricUntil" ⌋ then parseBoundedBinaryOp (λ n → LTL.MetricUntil (mkTs n) 0) obj
    else if ⌊ op ≟ "metricRelease" ⌋ then parseBoundedBinaryOp (λ n → LTL.MetricRelease (mkTs n) 0) obj
    else if ⌊ op ≟ "never" ⌋ then parseNeverOp obj
    else if ⌊ op ≟ "implies" ⌋ then parseImpliesOp obj
    else inj₁ Shape

  -- Parse atomic predicate (no recursive LTL parsing)
  parseAtomicOp : List (String × JSON) → ParseFail ⊎ (LTL SignalPredicate)
  parseAtomicOp obj = do
    predObj ← shape (lookupObject "predicate" obj)
    pred ← parseSignalPredicate predObj
    inj₂ (LTL.Atomic pred)

  -- Parse unary operator (Not, Next, Always, Eventually)
  parseUnaryOp : (LTL SignalPredicate → LTL SignalPredicate)
               → List (String × JSON) → ParseFail ⊎ (LTL SignalPredicate)
  parseUnaryOp ctor obj = do
    formula ← lookupAndParse "formula" obj
    inj₂ (ctor formula)

  -- Parse binary operator (And, Or, Until, Release)
  parseBinaryOp : (LTL SignalPredicate → LTL SignalPredicate → LTL SignalPredicate)
                → List (String × JSON) → ParseFail ⊎ (LTL SignalPredicate)
  parseBinaryOp ctor obj = do
    left ← lookupAndParse "left" obj
    right ← lookupAndParse "right" obj
    inj₂ (ctor left right)

  -- Parse bounded unary operator (MetricEventually, MetricAlways)
  parseBoundedOp : (ℕ → LTL SignalPredicate → LTL SignalPredicate)
                 → List (String × JSON) → ParseFail ⊎ (LTL SignalPredicate)
  parseBoundedOp ctor obj = do
    timebound ← shape (lookupNat "timebound" obj)
    formula ← lookupAndParse "formula" obj
    inj₂ (ctor timebound formula)

  -- Parse bounded binary operator (MetricUntil, MetricRelease)
  parseBoundedBinaryOp : (ℕ → LTL SignalPredicate → LTL SignalPredicate → LTL SignalPredicate)
                       → List (String × JSON) → ParseFail ⊎ (LTL SignalPredicate)
  parseBoundedBinaryOp ctor obj = do
    timebound ← shape (lookupNat "timebound" obj)
    left ← lookupAndParse "left" obj
    right ← lookupAndParse "right" obj
    inj₂ (ctor timebound left right)

  -- Parse "never" as Always(Not(formula))
  parseNeverOp : List (String × JSON) → ParseFail ⊎ (LTL SignalPredicate)
  parseNeverOp obj = do
    formula ← lookupAndParse "formula" obj
    inj₂ (LTL.Always (LTL.Not formula))

  -- Parse "implies" as Or(Not(antecedent), consequent)
  parseImpliesOp : List (String × JSON) → ParseFail ⊎ (LTL SignalPredicate)
  parseImpliesOp obj = do
    ant ← lookupAndParse "antecedent" obj
    cons ← lookupAndParse "consequent" obj
    inj₂ (LTL.Or (LTL.Not ant) cons)

-- ============================================================================
-- PUBLIC API
-- ============================================================================

-- Entry point: structural parse of a property JSON into the LTL ADT, carrying
-- the typed failure reason.  `inj₁ Shape` on malformed JSON shape (missing
-- operator discriminator, ill-typed sub-fields); `inj₁ (BadSignal …)` when a
-- `"signal"` value is not a valid DBC identifier (the single signal-name
-- decision lives in `Identifier.parseIdentifierField`, routed through
-- `signalField` — there is no separate diagnostic walk).  The adversarial
-- atom-count cap (`max-atom-count-per-property`, 1024) is enforced ONE LAYER UP
-- by `parseAllProperties` (`Protocol.Handlers`) as a typed `ParseErr
-- (InputBoundExceeded AtomCount …)` rejection, since it needs the constructed
-- tree's atom count.  Formatter-side bound preservation lives in
-- `DBC/Formatter/Bounded.agda` (cluster 8 e.4 length-map lemmas).
parseProperty : JSON → ParseFail ⊎ (LTL SignalPredicate)
parseProperty j = parseLTL j
