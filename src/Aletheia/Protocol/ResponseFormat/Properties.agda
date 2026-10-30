-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Correctness properties for response formatting.
--
-- Purpose: Prove format-response injectivity (Ack uniqueness), that every
-- number any reply writes is in the range `replyRange` gives its place
-- (`formatResponse-in-range`), and so in the range every binding's reader
-- decodes (`formatResponse-readable`).
-- Risk mitigated: Ack formatted as Violation or vice versa would cause
-- language bindings to misinterpret the result; a bound refusal echoing a
-- measured value of unbounded length would cost the host process its heap
-- while the reply is rendered, and pass the range bindings decode it into; a
-- number past the readers' range anywhere in a reply would fail the decoder
-- after the kernel answered.
module Aletheia.Protocol.ResponseFormat.Properties where

open import Data.Bool using (true; false; T)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _∷ʳ_)
open import Data.Nat using (suc; _≤_; _<_; _<ᵇ_; _≤ᵇ_; _^_; _∸_; s≤s; z≤n; s≤s⁻¹)
open import Data.Nat.Properties using (<ᵇ⇒<; <⇒<ᵇ; ≤⇒≯; ≮⇒≥; ≤-refl; ≤-trans; ≤ᵇ⇒≤; <⇒≤)
open import Data.Bool.Properties using (T?)
open import Relation.Nullary.Decidable using (recompute; _×?_)
open import Data.Integer using (ℤ; +_; -[1+_]; ∣_∣; -≤-; -≤+; +≤+) renaming (_≤_ to _≤ᶻ_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Rational using (ℚ)
open import Data.String using (String; toList) renaming (_++_ to _++ₛ_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

import Aletheia.Error as Err
open import Aletheia.Error using (showObserved; showBoundObserved)
open import Aletheia.Limits using
  (boundKindCode; boundKindLabel; observed-ceiling; saturateObserved; bound-ceiling; saturateBound; max-rational-component-magnitude
  ; Passes
  ; InputLengthBytes; NestingDepth; ArrayCardinality; IdentifierLength; StringLength; AtomCount
  ; PropertyCount; RationalComponentMagnitude)
open import Aletheia.DBC.Types using (IsError; IsWarning; ValidationIssue)
open import Aletheia.Parser.Position using (Position)
open import Aletheia.Prelude using (ℕtoℚ)
open import Aletheia.CAN.Batch.WireFits using (Fits; wireFits-components)
open import Aletheia.Protocol.JSON.Types using
  ( JSON; JNull; JBool; JNumber; JString; JArray; JObject; JStringS
  ; NumbersSatisfy; ListNumbersSatisfy; FieldsNumbersSatisfy; ComponentsWithin
  ; jsonDepth; Shallow; FieldsShallow )
open import Aletheia.Protocol.JSON.Shallow using (shallow-depth; map-shallow)
open import Aletheia.DBC.Formatter.Bounded using (dlcBytes-≤64)
open import Aletheia.Protocol.Message using (Success; Error;
  ExtractionResultsResponse; PropertyResponse; Ack; Complete; ValidationResponse; DBCResponse;
  ParsedDBCResponse; DBCTextResponse)
open import Aletheia.Protocol.Response using (PropertyResult; CounterexampleData; mkWarning; UncachedAtom)
open import Aletheia.Protocol.ResponseFormat using
  ( formatResponse; errorExtras; formatPropertyResult
  ; formatWarning; formatValidationIssue; formatSignalValue; formatSignalError; formatIssueSeverity
  ; formatIssueCode )
open import Aletheia.Protocol.ReplyRange using
  ( ValuesAt; FieldsValuesAt; InRange; TextIn; replyRange; replyText; replyPlaces
  ; oneOf; severities
  ; naturalAtMost; positiveAtMost; integerAtMost; rationalWithin; byteCount
  ; natural-in; positive-in; map-at; mapAll-at; at-satisfies )

-- ============================================================================
-- FORMAT-RESPONSE INJECTIVITY (Ack uniqueness)
-- ============================================================================

-- Ack is the only Response constructor mapping to the Ack JSON.
-- Each non-Ack case produces a JObject with ≥ 2 fields, while Ack has exactly 1.
-- Agda refutes the equality by list-length mismatch (x ∷ y ∷ ... ≢ z ∷ []).
-- This is the key lemma enabling end-to-end Ack soundness at the JSON level:
-- if the formatted response equals the Ack JSON, the response IS Ack.
formatResponse-ack-unique : ∀ r → formatResponse r ≡ formatResponse Ack → r ≡ Ack
formatResponse-ack-unique (Success _) ()
formatResponse-ack-unique (Error _) ()
formatResponse-ack-unique (ExtractionResultsResponse _ _ _ _) ()
-- PropertyResponse carries `List PropertyResult`.
-- The wire emit is `{"type": "property_batch", "results": [...]}` —
-- always a 2-field JObject regardless of list length, so the inhabitant
-- can never collapse to Ack's 1-field shape.  The single `_` covers the
-- singleton / batch cases uniformly.
formatResponse-ack-unique (PropertyResponse _ _) ()
formatResponse-ack-unique Ack _ = refl
formatResponse-ack-unique (Complete _ _) ()
formatResponse-ack-unique (DBCResponse _ _) ()
formatResponse-ack-unique (ValidationResponse _) ()
formatResponse-ack-unique (ParsedDBCResponse _ _ _) ()
formatResponse-ack-unique (DBCTextResponse _ _) ()

-- ============================================================================
-- A REFUSAL'S OBSERVED VALUE IS AT MOST THE CEILING
-- ============================================================================

-- The comparison `saturateObserved` and `showObserved` both decide by, read
-- as an order on naturals.
private
  past : ∀ {o} → (observed-ceiling <ᵇ o) ≡ true → observed-ceiling < o
  past {o} eq = <ᵇ⇒< observed-ceiling o (subst T (sym eq) tt)

  not-past : ∀ {o} → (observed-ceiling <ᵇ o) ≡ false → o ≤ observed-ceiling
  not-past eq = ≮⇒≥ (λ c<o → subst T eq (<⇒<ᵇ c<o))

-- The ceiling is the top of the unsigned 64-bit range.
observed-ceiling-is : observed-ceiling ≡ 2 ^ 64 ∸ 1
observed-ceiling-is = refl

-- A reported value never passes the ceiling.
saturateObserved-≤ : ∀ o → saturateObserved o ≤ observed-ceiling
saturateObserved-≤ o with observed-ceiling <ᵇ o in eq
... | true  = ≤-refl
... | false = not-past eq

-- A measured value at or below the ceiling is reported as it is.
saturateObserved-exact : ∀ {o} → o ≤ observed-ceiling → saturateObserved o ≡ o
saturateObserved-exact {o} o≤c with observed-ceiling <ᵇ o in eq
... | true  = ⊥-elim (≤⇒≯ o≤c (past eq))
... | false = refl

-- A measured value past the ceiling is reported as the ceiling.
saturateObserved-past : ∀ {o} → observed-ceiling < o → saturateObserved o ≡ observed-ceiling
saturateObserved-past {o} c<o with observed-ceiling <ᵇ o in eq
... | true  = refl
... | false = ⊥-elim (≤⇒≯ (not-past eq) c<o)

-- The message prints a measured value at or below the ceiling as it is ...
showObserved-exact : ∀ {o} → o ≤ observed-ceiling → showObserved o ≡ showℕ o
showObserved-exact {o} o≤c with observed-ceiling <ᵇ o in eq
... | true  = ⊥-elim (≤⇒≯ o≤c (past eq))
... | false = refl

-- ... and one past it as "at least" and the ceiling, never the value itself.
showObserved-past : ∀ {o} → observed-ceiling < o →
  showObserved o ≡ "at least " ++ₛ showℕ observed-ceiling
showObserved-past {o} c<o with observed-ceiling <ᵇ o in eq
... | true  = refl
... | false = ⊥-elim (≤⇒≯ (not-past eq) c<o)

-- The bound refusals' ceiling, read the same way.
private
  bound-past : ∀ {o} → (bound-ceiling <ᵇ o) ≡ true → bound-ceiling < o
  bound-past {o} eq = <ᵇ⇒< bound-ceiling o (subst T (sym eq) tt)

  bound-not-past : ∀ {o} → (bound-ceiling <ᵇ o) ≡ false → o ≤ bound-ceiling
  bound-not-past eq = ≮⇒≥ (λ c<o → subst T eq (<⇒<ᵇ c<o))

-- The bound refusals' ceiling is the top of the unsigned 128-bit range.
bound-ceiling-is : bound-ceiling ≡ 2 ^ 128 ∸ 1
bound-ceiling-is = refl

-- A bound refusal's reported value never passes its ceiling ...
saturateBound-≤ : ∀ o → saturateBound o ≤ bound-ceiling
saturateBound-≤ o with bound-ceiling <ᵇ o in eq
... | true  = ≤-refl
... | false = bound-not-past eq

-- ... is reported as it is at or below the ceiling ...
saturateBound-exact : ∀ {o} → o ≤ bound-ceiling → saturateBound o ≡ o
saturateBound-exact {o} o≤c with bound-ceiling <ᵇ o in eq
... | true  = ⊥-elim (≤⇒≯ o≤c (bound-past eq))
... | false = refl

-- ... and as the ceiling past it.
saturateBound-past : ∀ {o} → bound-ceiling < o → saturateBound o ≡ bound-ceiling
saturateBound-past {o} c<o with bound-ceiling <ᵇ o in eq
... | true  = refl
... | false = ⊥-elim (≤⇒≯ (bound-not-past eq) c<o)

-- A positive value stays positive through the ceiling.
saturateBound-pos : ∀ {o} → 1 ≤ o → 1 ≤ saturateBound o
saturateBound-pos {o} 1≤o with bound-ceiling <ᵇ o in eq
... | true  = ≤ᵇ⇒≤ 1 bound-ceiling tt
... | false = 1≤o

-- What a bound refusal carries, made relevant: its limit is at least 1 and
-- its measured value passed it, so both are at least 1.
passes-pos : ∀ {o l} → .(Passes o l) → 1 ≤ o × 1 ≤ l
passes-pos {o} {l} p =
  let (one , past) = recompute (T? (1 ≤ᵇ l) ×? T? (l <ᵇ o)) p
      1≤l = ≤ᵇ⇒≤ 1 l one
  in ≤-trans 1≤l (<⇒≤ (<ᵇ⇒< l o past)) , 1≤l

-- The message prints a measured value at or below the ceiling as it is ...
showBoundObserved-exact : ∀ {o} → o ≤ bound-ceiling → showBoundObserved o ≡ " " ++ₛ showℕ o
showBoundObserved-exact {o} o≤c with bound-ceiling <ᵇ o in eq
... | true  = ⊥-elim (≤⇒≯ o≤c (bound-past eq))
... | false = refl

-- ... and names no value past it.
showBoundObserved-past : ∀ {o} → bound-ceiling < o → showBoundObserved o ≡ ""
showBoundObserved-past {o} c<o with bound-ceiling <ᵇ o in eq
... | true  = refl
... | false = ⊥-elim (≤⇒≯ (bound-not-past eq) c<o)

-- A bound refusal's message prints its measured value through
-- `showBoundObserved` and its fields write it and the limit through
-- `saturateBound`; the `At` form delegates to both and adds `field`.
formatError-bound : ∀ k o l .(p : Passes o l) → Err.formatError (Err.InputBoundExceeded k o l p) ≡
  boundKindLabel k ++ₛ showBoundObserved o ++ₛ " exceeds limit " ++ₛ showℕ l
formatError-bound _ _ _ _ = refl

errorExtras-bound : ∀ k o l .(p : Passes o l) → errorExtras (Err.InputBoundExceeded k o l p) ≡
  ("bound_kind" , JStringS (boundKindCode k)) ∷
  ("observed"   , JNumber (ℕtoℚ (saturateBound o))) ∷
  ("limit"      , JNumber (ℕtoℚ (saturateBound l))) ∷ []
errorExtras-bound _ _ _ _ = refl

-- ============================================================================
-- EVERY NUMBER A REPLY WRITES IS IN THE READERS' RANGE
-- ============================================================================

-- Every binding's reader decodes a numerator as a sign and a magnitude of at
-- most 2^128-1, and a denominator at most 2^128-1.  Every row of
-- `replyRange` names a limit within that range, so a number in its place's
-- range is one every reader decodes.

-- The least numerator a reader decodes, -(2^128-1), as -[1+ (2^128-2)].
reader-floor : ℤ
reader-floor = -[1+ 340282366920938463463374607431768211454 ]

-- A rational every reader decodes.
InReaderRange : ℚ → Set
InReaderRange q =
  reader-floor ≤ᶻ ℚ.numerator q × ℚ.numerator q ≤ᶻ + bound-ceiling
  × suc (ℚ.denominator-1 q) ≤ bound-ceiling

-- The component bound against the 128-bit ceiling and the floor's
-- magnitude, by evaluation.
magnitude≤ceiling : max-rational-component-magnitude ≤ bound-ceiling
magnitude≤ceiling = ≤ᵇ⇒≤ max-rational-component-magnitude bound-ceiling tt

magnitude≤floor : max-rational-component-magnitude ≤ suc 340282366920938463463374607431768211454
magnitude≤floor = ≤ᵇ⇒≤ max-rational-component-magnitude (suc 340282366920938463463374607431768211454) tt

-- An integer of magnitude at most the component bound lies between the floor
-- and the ceiling.
int-in-range : ∀ z → ∣ z ∣ ≤ max-rational-component-magnitude
  → reader-floor ≤ᶻ z × z ≤ᶻ + bound-ceiling
int-in-range (+ n)    n≤ = -≤+ , +≤+ (≤-trans n≤ magnitude≤ceiling)
int-in-range -[1+ n ] n≤ = -≤- (s≤s⁻¹ (≤-trans n≤ magnitude≤floor)) , -≤+

-- A rational with both components within the bound is one every reader decodes.
components-readable : ∀ q → ComponentsWithin max-rational-component-magnitude q → InReaderRange q
components-readable q (n≤ , d≤) =
  proj₁ (int-in-range (ℚ.numerator q) n≤) , proj₂ (int-in-range (ℚ.numerator q) n≤)
  , ≤-trans d≤ magnitude≤ceiling

-- A claim implied by another lifts over a JSON value, number by number.
mutual
  satisfy-map : ∀ {P Q : ℚ → Set} → (∀ q → P q → Q q) → ∀ j → NumbersSatisfy P j → NumbersSatisfy Q j
  satisfy-map h JNull        _ = tt
  satisfy-map h (JBool _)    _ = tt
  satisfy-map h (JNumber q)  p = h q p
  satisfy-map h (JString _)  _ = tt
  satisfy-map h (JArray xs)  w = list-satisfy-map h xs w
  satisfy-map h (JObject fs) w = fields-satisfy-map h fs w

  list-satisfy-map : ∀ {P Q : ℚ → Set} → (∀ q → P q → Q q)
    → ∀ xs → ListNumbersSatisfy P xs → ListNumbersSatisfy Q xs
  list-satisfy-map h []       _        = tt
  list-satisfy-map h (x ∷ xs) (p , ps) = satisfy-map h x p , list-satisfy-map h xs ps

  fields-satisfy-map : ∀ {P Q : ℚ → Set} → (∀ q → P q → Q q)
    → ∀ fs → FieldsNumbersSatisfy P fs → FieldsNumbersSatisfy Q fs
  fields-satisfy-map h []        _        = tt
  fields-satisfy-map h (kv ∷ fs) (p , ps) = satisfy-map h (proj₂ kv) p , fields-satisfy-map h fs ps

-- A natural at most the 128-bit ceiling, written as a JSON number: its
-- numerator is `+ n` and its denominator 1.
wide-nat-readable : ∀ {n} → n ≤ bound-ceiling → InReaderRange (ℕtoℚ n)
wide-nat-readable n≤ = -≤+ , +≤+ n≤ , s≤s z≤n

-- Every row's range lies within the readers' range: its limit is within the
-- component bound (the form's instance argument).
@0 form-readable : ∀ m q → InRange m q → InReaderRange q
form-readable nothing _ ()
form-readable (just (naturalAtMost l ⦃ b ⦄)) _ (n , refl , n≤) =
  wide-nat-readable (≤-trans n≤ (≤-trans (≤ᵇ⇒≤ l max-rational-component-magnitude b) magnitude≤ceiling))
form-readable (just (positiveAtMost l ⦃ b ⦄)) _ (n , refl , _ , n≤) =
  wide-nat-readable (≤-trans n≤ (≤-trans (≤ᵇ⇒≤ l max-rational-component-magnitude b) magnitude≤ceiling))
form-readable (just (integerAtMost l ⦃ b ⦄)) _ (z , refl , z≤) =
  let r = int-in-range z (≤-trans z≤ (≤ᵇ⇒≤ l max-rational-component-magnitude b))
  in proj₁ r , proj₂ r , s≤s z≤n
form-readable (just (rationalWithin l ⦃ b ⦄)) q (n≤ , d≤) =
  let l≤ = ≤ᵇ⇒≤ l max-rational-component-magnitude b
  in components-readable q (≤-trans n≤ l≤ , ≤-trans d≤ l≤)
form-readable (just byteCount) _ (d , refl) =
  wide-nat-readable (≤-trans (dlcBytes-≤64 d) (≤ᵇ⇒≤ 64 bound-ceiling tt))

-- ============================================================================
-- EVERY NUMBER A REPLY WRITES IS IN ITS PLACE'S RANGE
-- ============================================================================

private
  @0 At : List String → Maybe String → JSON → Set
  At = ValuesAt replyPlaces

  @0 FieldsAt : List String → Maybe String → List (String × JSON) → Set
  FieldsAt = FieldsValuesAt replyPlaces

  -- A natural through `saturateObserved` and one through `saturateBound`,
  -- each at most its ceiling.
  @0 saturated-in : ∀ n → InRange (just (naturalAtMost observed-ceiling)) (ℕtoℚ (saturateObserved n))
  saturated-in n = natural-in _ (saturateObserved-≤ n)

  @0 boundSaturated-in : ∀ n → 1 ≤ n → InRange (just (positiveAtMost bound-ceiling)) (ℕtoℚ (saturateBound n))
  boundSaturated-in n 1≤n = positive-in _ (saturateBound-pos 1≤n) (saturateBound-≤ n)

  -- A validation issue's severity is one of the two its place lists, its
  -- code and detail any text, wherever the place's rows say so; an
  -- extraction error carries text only.
  @0 severity-in : ∀ s → TextIn (just (oneOf severities)) (toList (formatIssueSeverity s))
  severity-in IsError   = tt
  severity-in IsWarning = tt

  @0 issue-at : ∀ p t
    → (∀ s → TextIn (replyText (p ∷ʳ "severity") nothing) (toList (formatIssueSeverity s)))
    → (∀ cs → TextIn (replyText (p ∷ʳ "code") nothing) cs)
    → (∀ cs → TextIn (replyText (p ∷ʳ "detail") nothing) cs)
    → ∀ i → At p t (formatValidationIssue i)
  issue-at _ _ sev code detail i =
    sev (ValidationIssue.severity i)
    , code (toList (formatIssueCode (ValidationIssue.code i)))
    , detail (toList (ValidationIssue.detail i))
    , tt

  -- An issue at the two places issues sit, `issues` and a load's `warnings`.
  @0 issue-in-issues : ∀ i → At ("issues" ∷ []) nothing (formatValidationIssue i)
  issue-in-issues = issue-at ("issues" ∷ []) nothing severity-in (λ _ → tt) (λ _ → tt)

  @0 issue-in-warnings : ∀ i → At ("warnings" ∷ []) nothing (formatValidationIssue i)
  issue-in-warnings = issue-at ("warnings" ∷ []) nothing severity-in (λ _ → tt) (λ _ → tt)

  @0 signalError-at : ∀ e → At ("errors" ∷ []) nothing (formatSignalError e)
  signalError-at _ = tt , tt , tt

  -- A property result's index is saturated; a violation's timestamp carries
  -- its bound from the frame entry.
  @0 propertyResult-at : ∀ {t} r → At ("results" ∷ []) t (formatPropertyResult r)
  propertyResult-at (PropertyResult.Violation idx ce) =
    tt , tt , saturated-in idx , natural-in _ (CounterexampleData.tsBounded ce) , tt , tt
  propertyResult-at (PropertyResult.Satisfaction idx) = tt , tt , saturated-in idx , tt
  propertyResult-at (PropertyResult.Unresolved idx _) = tt , tt , saturated-in idx , tt , tt

  @0 warning-at : ∀ w → At ("warnings" ∷ []) nothing (formatWarning w)
  warning-at (mkWarning UncachedAtom idx _) = tt , saturated-in idx , tt , tt

  -- An extracted value the categoriser kept has both components within the
  -- component bound.
  @0 value-at : ∀ p → Fits p → At ("values" ∷ []) nothing (formatSignalValue p)
  value-at (_ , q) fits = tt , wireFits-components q fits , tt

  -- A bound refusal's kind is one its place lists.
  @0 boundKind-in : ∀ k → TextIn (replyText ("bound_kind" ∷ []) nothing) (toList (boundKindCode k))
  boundKind-in InputLengthBytes           = tt
  boundKind-in NestingDepth               = tt
  boundKind-in ArrayCardinality           = tt
  boundKind-in IdentifierLength           = tt
  boundKind-in StringLength               = tt
  boundKind-in AtomCount                  = tt
  boundKind-in PropertyCount              = tt
  boundKind-in RationalComponentMagnitude = tt

  -- Every number an error reply's structured fields carry is saturated; a
  -- bound refusal's two are positive.
  @0 bound-at : ∀ k o l .(p : Passes o l) → FieldsAt [] nothing (errorExtras (Err.InputBoundExceeded k o l p))
  bound-at k o l p =
    boundKind-in k , boundSaturated-in o (proj₁ (passes-pos {o} {l} p)) , boundSaturated-in l (proj₂ (passes-pos {o} {l} p)) , tt

  @0 parse-at : ∀ pe → FieldsAt [] nothing (errorExtras (Err.ParseErr pe))
  parse-at (Err.InvalidIdentifier (Err.InPart _) _) = tt , tt
  parse-at (Err.InvalidIdentifier (Err.AtText pos) _) =
    saturated-in (Position.line pos) , saturated-in (Position.column pos) , tt
  parse-at (Err.MissingField _) = tt
  parse-at (Err.InvalidByteOrder _) = tt
  parse-at (Err.InvalidPresence _) = tt
  parse-at Err.MissingSigned = tt
  parse-at (Err.InvalidSigned _) = tt
  parse-at (Err.NotAnObject _ _) = tt
  parse-at (Err.ExtCANIdOutOfRange _) = tt
  parse-at (Err.StdCANIdOutOfRange _) = tt
  parse-at (Err.DefaultCANIdOutOfRange _) = tt
  parse-at (Err.InvalidDLCBytes _) = tt
  parse-at Err.RootNotObject = tt
  parse-at Err.MissingSignalName = tt
  parse-at Err.SignalBitLengthZero = tt
  parse-at (Err.SignalStartBitExceedsFrame _ _) = tt
  parse-at (Err.SignalBitLengthExceedsFrame _ _) = tt
  parse-at (Err.SignalBigEndianOverflow _ _ _) = tt
  parse-at (Err.InvalidKind _ _) = tt
  parse-at (Err.NonTerminatingRational _) = tt
  parse-at Err.NonIntegerMultiplexValue = tt
  parse-at (Err.NonNaturalField _) = tt
  parse-at (Err.DLCCodeOutOfRange _) = tt
  parse-at (Err.PayloadLengthMismatch _ _) = tt
  parse-at (Err.PayloadByteOutOfRange _ _) = tt
  parse-at (Err.NonPositiveDenominator _) = tt
  parse-at (Err.SignalArrayLengthMismatch _ _ _) = tt
  parse-at (Err.TimestampPastWire _) = tt
  parse-at (Err.InContext _ _) = tt

  @0 handler-at : ∀ h → FieldsAt [] nothing (errorExtras (Err.HandlerErr h))
  handler-at Err.NoDBC                        = tt
  handler-at Err.AlreadyStreaming             = tt
  handler-at Err.NotStreaming                 = tt
  handler-at Err.StreamNotStarted             = tt
  handler-at Err.StreamActive                 = tt
  handler-at (Err.PropertyParseFailed _ _)    = tt
  handler-at (Err.PropertyRefused _)          = tt
  handler-at (Err.UnknownSignal _)            = tt
  handler-at (Err.ValidationFailed issues)    = tt , map-at issue-in-issues issues , tt
  handler-at (Err.TextRoundTripFailed issues) = tt , map-at issue-in-issues issues , tt
  handler-at (Err.NonMonotonicTimestamp _ _)  = tt
  handler-at (Err.WrappedParse _)             = tt
  handler-at (Err.WrappedFrame _)             = tt
  handler-at (Err.InContext _ inner)          = handler-at inner

  @0 errorExtras-at : ∀ e → FieldsAt [] nothing (errorExtras e)
  errorExtras-at (Err.ParseErr pe)     = parse-at pe
  errorExtras-at (Err.FrameErr _)      = tt
  errorExtras-at (Err.ExtractionErr _) = tt
  errorExtras-at (Err.RouteErr _)      = tt
  errorExtras-at (Err.HandlerErr h)    = handler-at h
  errorExtras-at (Err.DispatchErr Err.MissingTypeField)       = tt
  errorExtras-at (Err.DispatchErr (Err.UnknownMessageType _)) = tt
  errorExtras-at (Err.DispatchErr (Err.InvalidJSON pos))      =
    saturated-in (Position.line pos) , saturated-in (Position.column pos) , tt
  errorExtras-at (Err.DispatchErr Err.RequestNotObject)       = tt
  errorExtras-at (Err.DBCTextParseErr (Err.ParseFailure pos)) =
    saturated-in (Position.line pos) , saturated-in (Position.column pos) , tt
  errorExtras-at (Err.DBCTextParseErr (Err.TrailingInput pos stmt)) =
    saturated-in (Position.line pos) , saturated-in (Position.column pos) ,
    saturated-in (Position.line stmt) , saturated-in (Position.column stmt) , tt
  errorExtras-at (Err.DBCTextParseErr (Err.AttributeRefinementFailed _ _)) = tt
  errorExtras-at (Err.DBCTextParseErr (Err.SignalGeometryError _ _))       = tt
  errorExtras-at (Err.WithContext _ inner)          = errorExtras-at inner
  errorExtras-at (Err.InputBoundExceeded k o l p)     = bound-at k o l p
  errorExtras-at (Err.InputBoundExceededAt (Err.InPart _) k o l p) = tt , bound-at k o l p
  errorExtras-at (Err.InputBoundExceededAt (Err.AtText pos) k o l p) =
    saturated-in (Position.line pos) , saturated-in (Position.column pos) , bound-at k o l p
  errorExtras-at (Err.InvalidCharacter (Err.InField _ i) cp) =
    tt , saturated-in i , saturated-in cp , tt
  errorExtras-at (Err.InvalidCharacter (Err.InText pos) cp) =
    saturated-in (Position.line pos) , saturated-in (Position.column pos) , saturated-in cp , tt
  errorExtras-at (Err.KeywordName (Err.InPart _) _) = tt , tt , tt
  errorExtras-at (Err.KeywordName (Err.AtText pos) _) =
    saturated-in (Position.line pos) , saturated-in (Position.column pos) , tt , tt

-- THEOREM: every number `formatResponse` writes, for any reply, is in the
-- range `replyRange` gives its place.  Erased, since it reads the erased
-- proofs the replies carry.
@0 formatResponse-in-range : ∀ r → ValuesAt replyPlaces [] nothing (formatResponse r)
formatResponse-in-range (Success _) = tt , tt , tt
formatResponse-in-range (Error e)   = tt , tt , tt , errorExtras-at e
formatResponse-in-range (ExtractionResultsResponse values errors absent fit) =
  tt , mapAll-at value-at values fit , map-at signalError-at errors , map-at (λ _ → tt) absent , tt
formatResponse-in-range (PropertyResponse []       ())
formatResponse-in-range (PropertyResponse (r ∷ rs) _) = tt , map-at propertyResult-at (r ∷ rs) , tt
formatResponse-in-range Ack = tt , tt
formatResponse-in-range (Complete results warnings) =
  tt , map-at propertyResult-at results , map-at warning-at warnings , tt
formatResponse-in-range (DBCResponse json w) = tt , proj₁ w , tt
formatResponse-in-range (ValidationResponse issues) = tt , tt , map-at issue-in-issues issues , tt
formatResponse-in-range (ParsedDBCResponse json w warnings) =
  tt , proj₁ w , map-at issue-in-warnings warnings , tt
formatResponse-in-range (DBCTextResponse _ issues) = tt , tt , map-at issue-in-issues issues , tt

-- THEOREM: every number `formatResponse` writes, for any reply, has a
-- numerator of magnitude at most 2^128-1 and a denominator at most 2^128-1,
-- the range every binding's reader decodes.
@0 formatResponse-readable : ∀ r → NumbersSatisfy InReaderRange (formatResponse r)
formatResponse-readable r =
  at-satisfies (λ p t → form-readable (replyRange p t)) [] nothing (formatResponse r) (formatResponse-in-range r)

-- ============================================================================
-- DEPTH
-- ============================================================================

-- Every reply nests at most 8 deep: the reply, its formatted DBC (at most 7,
-- `formatDBC-shallow`), or an array of objects of primitives.
private
  @0 issue-shallow : ∀ k i → Shallow (suc k) (formatValidationIssue i)
  issue-shallow _ _ = tt , tt , tt , tt

  @0 propertyResult-shallow : ∀ k r → Shallow (suc k) (formatPropertyResult r)
  propertyResult-shallow _ (PropertyResult.Violation _ _) = tt , tt , tt , tt , tt , tt
  propertyResult-shallow _ (PropertyResult.Satisfaction _) = tt , tt , tt , tt
  propertyResult-shallow _ (PropertyResult.Unresolved _ _) = tt , tt , tt , tt , tt

  @0 warning-shallow : ∀ k w → Shallow (suc k) (formatWarning w)
  warning-shallow _ _ = tt , tt , tt , tt

  @0 value-shallow : ∀ k p → Shallow (suc k) (formatSignalValue p)
  value-shallow _ _ = tt , tt , tt

  @0 signalError-shallow : ∀ k e → Shallow (suc k) (formatSignalError e)
  signalError-shallow _ _ = tt , tt , tt

  @0 parse-shallow : ∀ k pe → FieldsShallow (suc (suc k)) (errorExtras (Err.ParseErr pe))
  parse-shallow k (Err.InvalidIdentifier (Err.InPart _) _) = tt , tt
  parse-shallow k (Err.InvalidIdentifier (Err.AtText _) _) = tt , tt , tt
  parse-shallow k (Err.MissingField _) = tt
  parse-shallow k (Err.InvalidByteOrder _) = tt
  parse-shallow k (Err.InvalidPresence _) = tt
  parse-shallow k Err.MissingSigned = tt
  parse-shallow k (Err.InvalidSigned _) = tt
  parse-shallow k (Err.NotAnObject _ _) = tt
  parse-shallow k (Err.ExtCANIdOutOfRange _) = tt
  parse-shallow k (Err.StdCANIdOutOfRange _) = tt
  parse-shallow k (Err.DefaultCANIdOutOfRange _) = tt
  parse-shallow k (Err.InvalidDLCBytes _) = tt
  parse-shallow k Err.RootNotObject = tt
  parse-shallow k Err.MissingSignalName = tt
  parse-shallow k Err.SignalBitLengthZero = tt
  parse-shallow k (Err.SignalStartBitExceedsFrame _ _) = tt
  parse-shallow k (Err.SignalBitLengthExceedsFrame _ _) = tt
  parse-shallow k (Err.SignalBigEndianOverflow _ _ _) = tt
  parse-shallow k (Err.InvalidKind _ _) = tt
  parse-shallow k (Err.NonTerminatingRational _) = tt
  parse-shallow k Err.NonIntegerMultiplexValue = tt
  parse-shallow k (Err.NonNaturalField _) = tt
  parse-shallow k (Err.DLCCodeOutOfRange _) = tt
  parse-shallow k (Err.PayloadLengthMismatch _ _) = tt
  parse-shallow k (Err.PayloadByteOutOfRange _ _) = tt
  parse-shallow k (Err.NonPositiveDenominator _) = tt
  parse-shallow k (Err.SignalArrayLengthMismatch _ _ _) = tt
  parse-shallow k (Err.TimestampPastWire _) = tt
  parse-shallow k (Err.InContext _ _) = tt

  @0 handler-shallow : ∀ k h → FieldsShallow (suc (suc k)) (errorExtras (Err.HandlerErr h))
  handler-shallow k Err.NoDBC                        = tt
  handler-shallow k Err.AlreadyStreaming             = tt
  handler-shallow k Err.NotStreaming                 = tt
  handler-shallow k Err.StreamNotStarted             = tt
  handler-shallow k Err.StreamActive                 = tt
  handler-shallow k (Err.PropertyParseFailed _ _)    = tt
  handler-shallow k (Err.PropertyRefused _)          = tt
  handler-shallow k (Err.UnknownSignal _)            = tt
  handler-shallow k (Err.ValidationFailed issues)    = tt , map-shallow formatValidationIssue (issue-shallow k) issues , tt
  handler-shallow k (Err.TextRoundTripFailed issues) = tt , map-shallow formatValidationIssue (issue-shallow k) issues , tt
  handler-shallow k (Err.NonMonotonicTimestamp _ _)  = tt
  handler-shallow k (Err.WrappedParse _)             = tt
  handler-shallow k (Err.WrappedFrame _)             = tt
  handler-shallow k (Err.InContext _ inner)          = handler-shallow k inner

  @0 errorExtras-shallow : ∀ k e → FieldsShallow (suc (suc k)) (errorExtras e)
  errorExtras-shallow k (Err.ParseErr pe)     = parse-shallow k pe
  errorExtras-shallow k (Err.FrameErr _)      = tt
  errorExtras-shallow k (Err.ExtractionErr _) = tt
  errorExtras-shallow k (Err.RouteErr _)      = tt
  errorExtras-shallow k (Err.HandlerErr h)    = handler-shallow k h
  errorExtras-shallow k (Err.DispatchErr Err.MissingTypeField)       = tt
  errorExtras-shallow k (Err.DispatchErr (Err.UnknownMessageType _)) = tt
  errorExtras-shallow k (Err.DispatchErr (Err.InvalidJSON _))        = tt , tt , tt
  errorExtras-shallow k (Err.DispatchErr Err.RequestNotObject)       = tt
  errorExtras-shallow k (Err.DBCTextParseErr (Err.ParseFailure _))   = tt , tt , tt
  errorExtras-shallow k (Err.DBCTextParseErr (Err.TrailingInput _ _)) = tt , tt , tt , tt , tt
  errorExtras-shallow k (Err.DBCTextParseErr (Err.AttributeRefinementFailed _ _)) = tt
  errorExtras-shallow k (Err.DBCTextParseErr (Err.SignalGeometryError _ _))       = tt
  errorExtras-shallow k (Err.WithContext _ inner)          = errorExtras-shallow k inner
  errorExtras-shallow k (Err.InputBoundExceeded _ _ _ _)     = tt , tt , tt , tt
  errorExtras-shallow k (Err.InputBoundExceededAt (Err.InPart _) _ _ _ _) = tt , tt , tt , tt , tt
  errorExtras-shallow k (Err.InputBoundExceededAt (Err.AtText _) _ _ _ _) = tt , tt , tt , tt , tt , tt
  errorExtras-shallow k (Err.InvalidCharacter (Err.InField _ _) _) = tt , tt , tt , tt
  errorExtras-shallow k (Err.InvalidCharacter (Err.InText _) _)    = tt , tt , tt , tt
  errorExtras-shallow k (Err.KeywordName (Err.InPart _) _)         = tt , tt , tt
  errorExtras-shallow k (Err.KeywordName (Err.AtText _) _)         = tt , tt , tt , tt

-- Every reply is within 8 levels.  Erased, since it reads the erased proofs
-- the DBC replies carry.
@0 formatResponse-shallow : ∀ r → Shallow 8 (formatResponse r)
formatResponse-shallow (Success _) = tt , tt , tt
formatResponse-shallow (Error e)   = tt , tt , tt , errorExtras-shallow 5 e
formatResponse-shallow (ExtractionResultsResponse values errors absent _) =
  tt , map-shallow formatSignalValue (value-shallow 5) values , map-shallow formatSignalError (signalError-shallow 5) errors
     , map-shallow JStringS (λ _ → tt) absent , tt
formatResponse-shallow (PropertyResponse results _) = tt , map-shallow formatPropertyResult (propertyResult-shallow 5) results , tt
formatResponse-shallow Ack = tt , tt
formatResponse-shallow (Complete results warnings) =
  tt , map-shallow formatPropertyResult (propertyResult-shallow 5) results , map-shallow formatWarning (warning-shallow 5) warnings , tt
formatResponse-shallow (DBCResponse json w) = tt , proj₂ w , tt
formatResponse-shallow (ValidationResponse issues) = tt , tt , map-shallow formatValidationIssue (issue-shallow 5) issues , tt
formatResponse-shallow (ParsedDBCResponse json w warnings) =
  tt , proj₂ w , map-shallow formatValidationIssue (issue-shallow 5) warnings , tt
formatResponse-shallow (DBCTextResponse _ issues) = tt , tt , map-shallow formatValidationIssue (issue-shallow 5) issues , tt

-- THEOREM: every reply nests at most 8 deep, below every binding reader's
-- nesting limit.
@0 formatResponse-depth : ∀ r → jsonDepth (formatResponse r) ≤ 8
formatResponse-depth r = shallow-depth 8 (formatResponse r) (formatResponse-shallow r)
