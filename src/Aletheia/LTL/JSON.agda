-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
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
-- Failure surface: the parser is reason-carrying: it returns `ParseFail ⊎ _`,
-- never a bare `Maybe`.  Every field is read through one reader that names an
-- absent key or a key of the wrong kind; a rational, an ordered pair, a
-- tolerance and a time bound are decided as they are read, and a signal name
-- in exactly ONE place (`decideSignal`, reached through `signalField`): the
-- identifier decision, then its presence among the loaded DBC's signals, the
-- predicate the caller passes.  The reason propagates up the single parse path
-- as `ParseFail`, and the handler renames the verdict to the wire error.
-- There is no second validity walk to keep in sync.
module Aletheia.LTL.JSON where

open import Data.String using (String; _≟_; fromList)
open import Data.Bool using (Bool; T?; if_then_else_)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Nat using (ℕ; suc) renaming (_≤ᵇ_ to _≤ᵇℕ_)
open import Data.Integer using (+_)
open import Data.Rational using (ℚ; 0ℚ; _≤ᵇ_; _/_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Aletheia.Prelude using (lookupByKey)
open import Aletheia.JSON using (JSON; JObject; JNumber; getString; getChars; getObject; getInt; getNat)
open import Aletheia.Error using
  ( Error; HandlerErr; HandlerError; UnknownSignal; InputBoundExceededAt; InPart
  ; PropertyRefusal; NotAnObject; FieldMissing; FieldNotOfKind; UnknownOperator; UnknownPredicate
  ; PartNotWhole; DenominatorNotPositive; MinExceedsMax; ToleranceNegative
  ; TimeBoundNegative; TimeBoundNotWhole; InPredicate
  ; FieldKind; AString; AnObject; ANumber; ARational; NumeratorPart; DenominatorPart )
open import Aletheia.Limits using (max-time-bound; RationalComponentMagnitude)
open import Aletheia.LTL.Syntax using (LTL)
open import Aletheia.Trace.Time using (mkTs)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate; ValueP; DeltaP)
import Aletheia.LTL.SignalPredicate as SP
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.JSONParser using (IdentRefusal; validateIdent; identError)

-- ============================================================================
-- PARSE FAILURE: the single reason-carrying result type
-- ============================================================================
--
-- `Refused r`: the JSON is no property, `r` saying why; the handler attaches
--   the property index and emits `HandlerErr (PropertyParseFailed …)`.
-- `BadSignal cs r`: the `"signal"` value `cs` failed `validateIdent`, the
--   decision a parsed DBC's names go through; the handler writes the
--   refusal as that route does.
-- `UnknownSignalName cs`: no signal of the loaded DBC is named `cs`; the
--   handler maps it to `HandlerErr (UnknownSignal …)`.
-- `TimeBoundPast n`: a whole time bound of `n` microseconds past
--   `max-time-bound`; the handler refuses it as a bound, `field` 'time bound'.
data ParseFail : Set where
  Refused           : PropertyRefusal → ParseFail
  BadSignal         : List Char → IdentRefusal → ParseFail
  UnknownSignalName : List Char → ParseFail
  TimeBoundPast     : ℕ → ParseFail

-- THE signal-name decision: the one identifier decision as a parsed DBC's
-- names get it (the grammar, the 129th character, a keyword, the first
-- non-ASCII character), then whether the loaded DBC carries the name
-- (`known`, the handler's view of the DBC).
decideSignal : (List Char → Bool) → List Char → ParseFail ⊎ Identifier
decideSignal known cs with validateIdent cs
... | inj₁ r = inj₁ (BadSignal cs r)
... | inj₂ i = if known cs then inj₂ i else inj₁ (UnknownSignalName cs)

-- ============================================================================
-- VALUE DECISIONS (public, so the round-trip proofs can name them)
-- ============================================================================

-- A range in order, carrying the decision; out of order, refused.
ordered : Identifier → (lo hi : ℚ) → ParseFail ⊎ SignalPredicate
ordered s lo hi with T? (lo ≤ᵇ hi)
... | yes w = inj₂ (ValueP (SP.Between s lo hi w))
... | no _  = inj₁ (Refused (MinExceedsMax lo hi))

-- A tolerance that is no distance (negative) is refused.
tolerant : Identifier → (tol : ℚ) → ParseFail ⊎ SignalPredicate
tolerant s tol with T? (0ℚ ≤ᵇ tol)
... | yes w = inj₂ (DeltaP (SP.StableWithin s tol w))
... | no _  = inj₁ (Refused (ToleranceNegative tol))

-- A time bound is a whole, non-negative number of microseconds at most
-- `max-time-bound`.  A negative number is refused as negative before its
-- wholeness is asked.
timeBound : ℚ → ParseFail ⊎ ℕ
timeBound r with getNat (JNumber r)
... | just n  = if n ≤ᵇℕ max-time-bound then inj₂ n else inj₁ (TimeBoundPast n)
... | nothing = inj₁ (Refused (if 0ℚ ≤ᵇ r then TimeBoundNotWhole r else TimeBoundNegative r))

-- A {numerator, denominator} object's two numbers: each whole, the
-- denominator positive.
fraction : String → ℚ → ℚ → ParseFail ⊎ ℚ
fraction key n d with getInt (JNumber n) | getInt (JNumber d)
... | nothing  | _              = inj₁ (Refused (PartNotWhole key NumeratorPart n))
... | just _   | nothing        = inj₁ (Refused (PartNotWhole key DenominatorPart d))
... | just num | just (+ suc k) = inj₂ (num / suc k)
... | just _   | just _         = inj₁ (Refused (DenominatorNotPositive key d))

-- Every parser below reads signal names against one `known` predicate.
module _ (known : List Char → Bool) where

  -- ============================================================================
  -- FIELD READERS (internal helpers)
  -- ============================================================================

  private
    -- Error-monad bind for `ParseFail ⊎ _` (short-circuits on `inj₁`).  This is
    -- the `_>>=_` the `do`-blocks below desugar against (the Maybe one is not in
    -- scope), so the typed failure threads through every parser uniformly.
    _>>=_ : ∀ {A B : Set} → ParseFail ⊎ A → (A → ParseFail ⊎ B) → ParseFail ⊎ B
    inj₁ e >>= _ = inj₁ e
    inj₂ a >>= f = f a

    -- THE field reader: an absent key and a key of the wrong kind each say so.
    readField : ∀ {A : Set} → (JSON → Maybe A) → FieldKind → String → List (String × JSON) → ParseFail ⊎ A
    readField get kind key obj with lookupByKey key obj
    ... | nothing = inj₁ (Refused (FieldMissing key))
    ... | just j  = maybe inj₂ (inj₁ (Refused (FieldNotOfKind key kind))) (get j)

    -- A rational field: a JSON number, or a {numerator, denominator} object
    -- of two numbers decided by `fraction`; anything else is no rational.
    fractionObject : String → List (String × JSON) → ParseFail ⊎ ℚ
    fractionObject key fs with lookupByKey "numerator" fs | lookupByKey "denominator" fs
    ... | just (JNumber n) | just (JNumber d) = fraction key n d
    ... | _                | _                = inj₁ (Refused (FieldNotOfKind key ARational))

    rationalOf : String → JSON → ParseFail ⊎ ℚ
    rationalOf _   (JNumber r)  = inj₂ r
    rationalOf key (JObject fs) = fractionObject key fs
    rationalOf key _            = inj₁ (Refused (FieldNotOfKind key ARational))

    rationalField : String → List (String × JSON) → ParseFail ⊎ ℚ
    rationalField key obj with lookupByKey key obj
    ... | nothing = inj₁ (Refused (FieldMissing key))
    ... | just j  = rationalOf key j

    timeBoundField : List (String × JSON) → ParseFail ⊎ ℕ
    timeBoundField obj with lookupByKey "timebound" obj
    ... | nothing          = inj₁ (Refused (FieldMissing "timebound"))
    ... | just (JNumber r) = timeBound r
    ... | just _           = inj₁ (Refused (FieldNotOfKind "timebound" ANumber))

    -- A predicate's own refusal names the predicate first.
    inPredicate : ∀ {A : Set} → String → ParseFail ⊎ A → ParseFail ⊎ A
    inPredicate p (inj₁ (Refused r)) = inj₁ (Refused (InPredicate p r))
    inPredicate _ other              = other

    -- THE signal-name parse point: read `"signal"` and run the single
    -- decision.  Every predicate parser routes its signal name through here.
    signalField : List (String × JSON) → ParseFail ⊎ Identifier
    signalField obj = do
      sigChars ← readField getChars AString "signal" obj
      decideSignal known sigChars

    parseEquals : List (String × JSON) → ParseFail ⊎ SignalPredicate
    parseEquals obj = do
      signal ← signalField obj
      value ← rationalField "value" obj
      inj₂ (ValueP (SP.Equals signal value))

    parseLessThan : List (String × JSON) → ParseFail ⊎ SignalPredicate
    parseLessThan obj = do
      signal ← signalField obj
      value ← rationalField "value" obj
      inj₂ (ValueP (SP.LessThan signal value))

    parseGreaterThan : List (String × JSON) → ParseFail ⊎ SignalPredicate
    parseGreaterThan obj = do
      signal ← signalField obj
      value ← rationalField "value" obj
      inj₂ (ValueP (SP.GreaterThan signal value))

    parseBetween : List (String × JSON) → ParseFail ⊎ SignalPredicate
    parseBetween obj = do
      signal ← signalField obj
      minVal ← rationalField "min" obj
      maxVal ← rationalField "max" obj
      ordered signal minVal maxVal

    parseLessThanOrEqual : List (String × JSON) → ParseFail ⊎ SignalPredicate
    parseLessThanOrEqual obj = do
      signal ← signalField obj
      value ← rationalField "value" obj
      inj₂ (ValueP (SP.LessThanOrEqual signal value))

    parseGreaterThanOrEqual : List (String × JSON) → ParseFail ⊎ SignalPredicate
    parseGreaterThanOrEqual obj = do
      signal ← signalField obj
      value ← rationalField "value" obj
      inj₂ (ValueP (SP.GreaterThanOrEqual signal value))

    parseChangedBy : List (String × JSON) → ParseFail ⊎ SignalPredicate
    parseChangedBy obj = do
      signal ← signalField obj
      delta ← rationalField "delta" obj
      inj₂ (DeltaP (SP.ChangedBy signal delta))

    parseStableWithin : List (String × JSON) → ParseFail ⊎ SignalPredicate
    parseStableWithin obj = do
      signal ← signalField obj
      tolerance ← rationalField "tolerance" obj
      tolerant signal tolerance

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
    ... | nothing = inj₁ (Refused (UnknownPredicate predType))
    ... | just parser = inPredicate predType (parser obj)

  -- Parse a signal predicate from JSON object fields
  parseSignalPredicate : List (String × JSON) → ParseFail ⊎ SignalPredicate
  parseSignalPredicate obj = do
    predType ← readField getString AString "predicate" obj
    dispatchPredicate predType obj

  -- ============================================================================
  -- LTL FORMULA PARSING - Structurally recursive on JSON input
  -- ============================================================================

  mutual
    -- Parse an LTL formula from JSON: the property itself, which is no
    -- property unless it is an object.
    parseLTL : JSON → ParseFail ⊎ (LTL SignalPredicate)
    parseLTL (JObject obj) = parseFormula obj
    parseLTL _ = inj₁ (Refused NotAnObject)

    -- A formula's fields: its operator, then what the operator reads.
    parseFormula : List (String × JSON) → ParseFail ⊎ (LTL SignalPredicate)
    parseFormula obj = do
      op ← readField getString AString "operator" obj
      dispatchOperator op obj

    -- Walk the field list to find a key, then recursively parse its JSON value.
    -- This makes the structural decrease visible to Agda's termination checker:
    -- the value v in (k , v) ∷ rest is a sub-component of the enclosing JObject.
    lookupAndParse : String → List (String × JSON) → ParseFail ⊎ (LTL SignalPredicate)
    lookupAndParse key [] = inj₁ (Refused (FieldMissing key))
    lookupAndParse key ((k , v) ∷ rest) =
      if ⌊ key ≟ k ⌋ then parseSub key v
      else lookupAndParse key rest

    -- A sub-formula held under `key`, which is no formula unless an object.
    parseSub : String → JSON → ParseFail ⊎ (LTL SignalPredicate)
    parseSub _   (JObject obj) = parseFormula obj
    parseSub key _             = inj₁ (Refused (FieldNotOfKind key AnObject))

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
      -- Lift the decided ℕ microseconds → `Timestamp μs` via `mkTs` at the parse
      -- boundary so the dimensional invariant holds inside the kernel.
      else if ⌊ op ≟ "metricEventually" ⌋ then parseBoundedOp (λ n → LTL.MetricEventually (mkTs n) 0) obj
      else if ⌊ op ≟ "metricAlways" ⌋ then parseBoundedOp (λ n → LTL.MetricAlways (mkTs n) 0) obj
      else if ⌊ op ≟ "metricUntil" ⌋ then parseBoundedBinaryOp (λ n → LTL.MetricUntil (mkTs n) 0) obj
      else if ⌊ op ≟ "metricRelease" ⌋ then parseBoundedBinaryOp (λ n → LTL.MetricRelease (mkTs n) 0) obj
      else if ⌊ op ≟ "never" ⌋ then parseNeverOp obj
      else if ⌊ op ≟ "implies" ⌋ then parseImpliesOp obj
      else inj₁ (Refused (UnknownOperator op))

    -- Parse atomic predicate (no recursive LTL parsing)
    parseAtomicOp : List (String × JSON) → ParseFail ⊎ (LTL SignalPredicate)
    parseAtomicOp obj = do
      predObj ← readField getObject AnObject "predicate" obj
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
      timebound ← timeBoundField obj
      formula ← lookupAndParse "formula" obj
      inj₂ (ctor timebound formula)

    -- Parse bounded binary operator (MetricUntil, MetricRelease)
    parseBoundedBinaryOp : (ℕ → LTL SignalPredicate → LTL SignalPredicate → LTL SignalPredicate)
                         → List (String × JSON) → ParseFail ⊎ (LTL SignalPredicate)
    parseBoundedBinaryOp ctor obj = do
      timebound ← timeBoundField obj
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

-- The wire error of a property read that failed.  `place` puts a refusal's
-- reason after the property's index (`PropertyParseFailed i`, set_properties)
-- or alone (`PropertyRefused`, the build-time property check); every other
-- verdict answers alike on both routes:
--   * `Refused r`: the JSON is no property, answered `place r`.
--   * `BadSignal cs r`: `cs` refused by the identifier decision, answered as
--     a parsed DBC's name is for `r` (`identError`), from the `signal` slot.
--   * `UnknownSignalName cs`: no signal of the DBC carries the name,
--     answered `HandlerErr (UnknownSignal …)`.
--   * `TimeBoundPast n`: a time bound past `max-time-bound`, answered as a
--     bound refusal, `field` 'time bound'.
parseFailError : (PropertyRefusal → HandlerError) → ParseFail → Error
parseFailError place (Refused r) = HandlerErr (place r)
parseFailError _ (BadSignal cs r) = identError "signal" cs r
parseFailError _ (UnknownSignalName cs) = HandlerErr (UnknownSignal (fromList cs))
parseFailError _ (TimeBoundPast n) =
  InputBoundExceededAt (InPart "time bound") RationalComponentMagnitude n max-time-bound

-- Entry point: structural parse of a property JSON into the LTL ADT, carrying
-- the typed failure reason: a `Refused` reason for JSON that is no property,
-- the signal-name verdicts of `decideSignal` against `known`, the loaded
-- DBC's signals, as each name is read, and a time bound past its limit.  The
-- adversarial atom-count cap (`max-atom-count-per-property`, 1024) is
-- enforced ONE LAYER UP by `parseAllProperties` (`Protocol.Handlers`) as a
-- typed `ParseErr (InputBoundExceeded AtomCount …)` rejection, since it needs
-- the constructed tree's atom count.  Formatter-side bound preservation lives
-- in `DBC/Formatter/Bounded.agda` (length-map lemmas).
parseProperty : (List Char → Bool) → JSON → ParseFail ⊎ (LTL SignalPredicate)
parseProperty known j = parseLTL known j
