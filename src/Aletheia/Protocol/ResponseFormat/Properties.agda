-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Correctness properties for response formatting.
--
-- Purpose: Prove format-response injectivity (Ack uniqueness), that an
-- error reply's `observed` never passes `observed-ceiling`, and that every
-- number any reply writes is in the range every binding's reader decodes
-- (`formatResponse-readable`).
-- Risk mitigated: Ack formatted as Violation or vice versa would cause
-- language bindings to misinterpret the result; a bound refusal echoing a
-- measured value of unbounded length would cost the host process its heap
-- while the reply is rendered, and pass the range bindings decode it into; a
-- number past the readers' range anywhere in a reply would fail the decoder
-- after the kernel answered.
module Aletheia.Protocol.ResponseFormat.Properties where

open import Data.Bool using (true; false; T)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Nat using (suc; _≤_; _<_; _<ᵇ_; _^_; _∸_; s≤s; z≤n)
open import Data.Nat.Properties using (<ᵇ⇒<; <⇒<ᵇ; <⇒≤; ≤⇒≯; ≮⇒≥; ≤-refl; ≤-trans; ≤ᵇ⇒≤)
open import Data.Integer using (ℤ; +_; -[1+_]; ∣_∣; -≤-; -≤+; +≤+) renaming (_≤_ to _≤ᶻ_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.Rational using (ℚ)
open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

import Aletheia.Error as Err
open import Aletheia.Error using (showObserved)
open import Aletheia.Limits using
  (boundKindCode; boundKindLabel; observed-ceiling; saturateObserved; max-rational-component-magnitude)
open import Aletheia.Parser.Position using (Position)
open import Aletheia.Prelude using (ℕtoℚ)
open import Aletheia.CAN.Batch.WireFits using (Fits; wireFits-components)
open import Aletheia.Protocol.JSON.Types using
  ( JSON; JNull; JBool; JNumber; JString; JArray; JObject; JStringS
  ; NumbersSatisfy; ListNumbersSatisfy; FieldsNumbersSatisfy; ComponentsWithin )
open import Aletheia.Protocol.Message using (Success; Error;
  ExtractionResultsResponse; PropertyResponse; Ack; Complete; ValidationResponse; DBCResponse;
  ParsedDBCResponse; DBCTextResponse)
open import Aletheia.Protocol.Response using (PropertyResult; CounterexampleData; Warning)
open import Aletheia.Protocol.ResponseFormat using
  ( formatResponse; errorExtras; saturated; formatPropertyResult
  ; formatWarning; formatValidationIssue; formatSignalValue; formatSignalError )

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
-- empty / singleton / batch cases uniformly.
formatResponse-ack-unique (PropertyResponse _) ()
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

-- A bound refusal's message prints its measured value through `showObserved`
-- and its fields write it and the limit through `saturateObserved`; the `At`
-- form delegates to both and adds `field`.
formatError-bound : ∀ k o l → Err.formatError (Err.InputBoundExceeded k o l) ≡
  boundKindLabel k ++ₛ " " ++ₛ showObserved o ++ₛ " exceeds limit " ++ₛ showℕ l
formatError-bound _ _ _ = refl

errorExtras-bound : ∀ k o l → errorExtras (Err.InputBoundExceeded k o l) ≡
  ("bound_kind" , JStringS (boundKindCode k)) ∷
  ("observed"   , JNumber (ℕtoℚ (saturateObserved o))) ∷
  ("limit"      , JNumber (ℕtoℚ (saturateObserved l))) ∷ []
errorExtras-bound _ _ _ = refl

-- An entry of a reply's fields keyed `observed` carries a natural at most the
-- ceiling.
ObservedWithin : String × JSON → Set
ObservedWithin (key , value) =
  key ≡ "observed" → ∃[ m ] (value ≡ JNumber (ℕtoℚ m) × m ≤ observed-ceiling)

-- The fields of a reply's top-level object.
replyFields : JSON → List (String × JSON)
replyFields (JObject fields) = fields
replyFields _                = []

private
  bound-within : ∀ k o l → All ObservedWithin (errorExtras (Err.InputBoundExceeded k o l))
  bound-within _ o _ =
    (λ ()) ∷ᵃ (λ _ → saturateObserved o , refl , saturateObserved-≤ o) ∷ᵃ (λ ()) ∷ᵃ []ᵃ

  handler-within : ∀ h → All ObservedWithin (errorExtras (Err.HandlerErr h))
  handler-within Err.NoDBC                       = []ᵃ
  handler-within Err.AlreadyStreaming            = []ᵃ
  handler-within Err.NotStreaming                = []ᵃ
  handler-within Err.StreamNotStarted            = []ᵃ
  handler-within Err.StreamActive                = []ᵃ
  handler-within (Err.PropertyParseFailed _)     = []ᵃ
  handler-within (Err.ValidationFailed _)        = (λ ()) ∷ᵃ (λ ()) ∷ᵃ []ᵃ
  handler-within (Err.TextRoundTripFailed _)     = (λ ()) ∷ᵃ (λ ()) ∷ᵃ []ᵃ
  handler-within (Err.NonMonotonicTimestamp _ _) = []ᵃ
  handler-within (Err.WrappedParse _)            = []ᵃ
  handler-within (Err.WrappedFrame _)            = []ᵃ
  handler-within (Err.InContext _ inner)         = handler-within inner

-- Every `observed` an error reply's fields carry is at most the ceiling,
-- whatever wraps the refusal.
errorExtras-observed-within : ∀ e → All ObservedWithin (errorExtras e)
errorExtras-observed-within (Err.ParseErr _)      = []ᵃ
errorExtras-observed-within (Err.FrameErr _)      = []ᵃ
errorExtras-observed-within (Err.ExtractionErr _) = []ᵃ
errorExtras-observed-within (Err.RouteErr _)      = []ᵃ
errorExtras-observed-within (Err.HandlerErr h)    = handler-within h
errorExtras-observed-within (Err.DispatchErr Err.MissingTypeField)       = []ᵃ
errorExtras-observed-within (Err.DispatchErr (Err.UnknownMessageType _)) = []ᵃ
errorExtras-observed-within (Err.DispatchErr (Err.InvalidJSON _))        = (λ ()) ∷ᵃ (λ ()) ∷ᵃ []ᵃ
errorExtras-observed-within (Err.DispatchErr Err.RequestNotObject)       = []ᵃ
errorExtras-observed-within (Err.DBCTextParseErr (Err.ParseFailure _))   = (λ ()) ∷ᵃ (λ ()) ∷ᵃ []ᵃ
errorExtras-observed-within (Err.DBCTextParseErr (Err.TrailingInput _ _)) =
  (λ ()) ∷ᵃ (λ ()) ∷ᵃ (λ ()) ∷ᵃ (λ ()) ∷ᵃ []ᵃ
errorExtras-observed-within (Err.DBCTextParseErr (Err.AttributeRefinementFailed _ _)) = []ᵃ
errorExtras-observed-within (Err.DBCTextParseErr (Err.SignalGeometryError _ _))       = []ᵃ
errorExtras-observed-within (Err.WithContext _ inner)          = errorExtras-observed-within inner
errorExtras-observed-within (Err.InputBoundExceeded k o l)     = bound-within k o l
errorExtras-observed-within (Err.InputBoundExceededAt _ k o l) = (λ ()) ∷ᵃ bound-within k o l

-- The theorem over the whole reply: every top-level `observed` an error
-- response writes is at most `observed-ceiling`.
formatResponse-error-observed-within :
  ∀ e → All ObservedWithin (replyFields (formatResponse (Error e)))
formatResponse-error-observed-within e =
  (λ ()) ∷ᵃ (λ ()) ∷ᵃ (λ ()) ∷ᵃ errorExtras-observed-within e

-- ============================================================================
-- EVERY NUMBER A REPLY WRITES IS IN THE READERS' RANGE
-- ============================================================================

-- Every binding's reader decodes a numerator in [-2^63, 2^64-1] and a
-- denominator at most 2^64-1.  A natural the formatter saturates is at most
-- the ceiling; a timestamp arrives with its bound
-- (`CounterexampleData.tsBounded`); a DBC's numbers and an extracted value's
-- components are within `max-rational-component-magnitude`, which is below
-- the ceiling and at most 2^63-1, so a negative numerator among them is at
-- least -(2^63-1).

-- The least numerator a reader decodes, -2^63, as the integer -[1+ (2^63-1)].
reader-floor : ℤ
reader-floor = -[1+ 9223372036854775807 ]

-- A rational every reader decodes.
InReaderRange : ℚ → Set
InReaderRange q =
  reader-floor ≤ᶻ ℚ.numerator q × ℚ.numerator q ≤ᶻ + observed-ceiling
  × suc (ℚ.denominator-1 q) ≤ observed-ceiling

-- The component bound against the ceiling and the floor's magnitude, by evaluation.
magnitude≤ceiling : max-rational-component-magnitude ≤ observed-ceiling
magnitude≤ceiling = ≤ᵇ⇒≤ max-rational-component-magnitude observed-ceiling tt

magnitude≤floor : max-rational-component-magnitude ≤ 9223372036854775807
magnitude≤floor = ≤ᵇ⇒≤ max-rational-component-magnitude 9223372036854775807 tt

-- An integer of magnitude at most the component bound lies between the floor
-- and the ceiling.
int-in-range : ∀ z → ∣ z ∣ ≤ max-rational-component-magnitude
  → reader-floor ≤ᶻ z × z ≤ᶻ + observed-ceiling
int-in-range (+ n)    n≤ = -≤+ , +≤+ (≤-trans n≤ magnitude≤ceiling)
int-in-range -[1+ n ] n≤ = -≤- (≤-trans (<⇒≤ n≤) magnitude≤floor) , -≤+

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

-- Every number in the readers' range.
Readable : JSON → Set
Readable = NumbersSatisfy InReaderRange

ListReadable : List JSON → Set
ListReadable = ListNumbersSatisfy InReaderRange

FieldsReadable : List (String × JSON) → Set
FieldsReadable = FieldsNumbersSatisfy InReaderRange

-- An array of formatted elements, each readable ...
map-readable : ∀ {A : Set} {f : A → JSON} → (∀ x → Readable (f x)) → ∀ xs → ListReadable (map f xs)
map-readable h []       = tt
map-readable h (x ∷ xs) = h x , map-readable h xs

-- ... and the same with a premise per element.
mapAll-readable : ∀ {A : Set} {f : A → JSON} {P : A → Set}
  → (∀ x → P x → Readable (f x)) → ∀ xs → All P xs → ListReadable (map f xs)
mapAll-readable h []       []ᵃ        = tt
mapAll-readable h (x ∷ xs) (p ∷ᵃ ps) = h x p , mapAll-readable h xs ps

-- A natural at most the ceiling, written as a JSON number: its numerator is
-- `+ n` and its denominator 1.
nat-readable : ∀ {n} → n ≤ observed-ceiling → Readable (JNumber (ℕtoℚ n))
nat-readable n≤ = -≤+ , +≤+ n≤ , s≤s z≤n

-- A saturated natural is at most the ceiling.
saturated-readable : ∀ n → Readable (saturated n)
saturated-readable n = nat-readable (saturateObserved-≤ n)

-- A validation issue carries strings only.
issue-readable : ∀ i → Readable (formatValidationIssue i)
issue-readable _ = tt , tt , tt , tt

-- A property result's index is saturated; a violation's timestamp carries
-- its bound from the frame entry.
@0 propertyResult-readable : ∀ r → Readable (formatPropertyResult r)
propertyResult-readable (PropertyResult.Violation idx ce) =
  tt , tt , saturated-readable idx , nat-readable (CounterexampleData.tsBounded ce) , tt , tt
propertyResult-readable (PropertyResult.Satisfaction idx) = tt , tt , saturated-readable idx , tt
propertyResult-readable (PropertyResult.Unresolved idx _) = tt , tt , saturated-readable idx , tt , tt

warning-readable : ∀ w → Readable (formatWarning w)
warning-readable w = tt , saturated-readable (Warning.propertyIndex w) , tt , tt

-- An extracted value the categoriser kept has both components within the
-- component bound, so every reader decodes it; an extraction error is strings.
@0 value-readable : ∀ p → Fits p → Readable (formatSignalValue p)
value-readable (_ , q) fits = tt , components-readable q (wireFits-components q fits) , tt

signalError-readable : ∀ e → Readable (formatSignalError e)
signalError-readable _ = tt , tt , tt

-- Every number an error reply's structured fields carry is saturated.
private
  bound-readable : ∀ k o l → FieldsReadable (errorExtras (Err.InputBoundExceeded k o l))
  bound-readable _ o l = tt , saturated-readable o , saturated-readable l , tt

  handler-readable : ∀ h → FieldsReadable (errorExtras (Err.HandlerErr h))
  handler-readable Err.NoDBC                       = tt
  handler-readable Err.AlreadyStreaming            = tt
  handler-readable Err.NotStreaming                = tt
  handler-readable Err.StreamNotStarted            = tt
  handler-readable Err.StreamActive                = tt
  handler-readable (Err.PropertyParseFailed _)     = tt
  handler-readable (Err.ValidationFailed issues)   = tt , map-readable issue-readable issues , tt
  handler-readable (Err.TextRoundTripFailed issues) = tt , map-readable issue-readable issues , tt
  handler-readable (Err.NonMonotonicTimestamp _ _) = tt
  handler-readable (Err.WrappedParse _)            = tt
  handler-readable (Err.WrappedFrame _)            = tt
  handler-readable (Err.InContext _ inner)         = handler-readable inner

errorExtras-readable : ∀ e → FieldsReadable (errorExtras e)
errorExtras-readable (Err.ParseErr _)      = tt
errorExtras-readable (Err.FrameErr _)      = tt
errorExtras-readable (Err.ExtractionErr _) = tt
errorExtras-readable (Err.RouteErr _)      = tt
errorExtras-readable (Err.HandlerErr h)    = handler-readable h
errorExtras-readable (Err.DispatchErr Err.MissingTypeField)       = tt
errorExtras-readable (Err.DispatchErr (Err.UnknownMessageType _)) = tt
errorExtras-readable (Err.DispatchErr (Err.InvalidJSON pos))      =
  saturated-readable (Position.line pos) , saturated-readable (Position.column pos) , tt
errorExtras-readable (Err.DispatchErr Err.RequestNotObject)       = tt
errorExtras-readable (Err.DBCTextParseErr (Err.ParseFailure pos)) =
  saturated-readable (Position.line pos) , saturated-readable (Position.column pos) , tt
errorExtras-readable (Err.DBCTextParseErr (Err.TrailingInput pos stmt)) =
  saturated-readable (Position.line pos) , saturated-readable (Position.column pos) ,
  saturated-readable (Position.line stmt) , saturated-readable (Position.column stmt) , tt
errorExtras-readable (Err.DBCTextParseErr (Err.AttributeRefinementFailed _ _)) = tt
errorExtras-readable (Err.DBCTextParseErr (Err.SignalGeometryError _ _))       = tt
errorExtras-readable (Err.WithContext _ inner)          = errorExtras-readable inner
errorExtras-readable (Err.InputBoundExceeded k o l)     = bound-readable k o l
errorExtras-readable (Err.InputBoundExceededAt _ k o l) = tt , bound-readable k o l

-- THEOREM: every number `formatResponse` writes, for any reply, has a
-- numerator in [-2^63, 2^64-1] and a denominator at most 2^64-1, the range
-- every binding's reader decodes.  Erased, since it reads the erased proofs
-- the replies carry.
@0 formatResponse-readable : ∀ r → NumbersSatisfy InReaderRange (formatResponse r)
formatResponse-readable (Success _) = tt , tt , tt
formatResponse-readable (Error e)   = tt , tt , tt , errorExtras-readable e
formatResponse-readable (ExtractionResultsResponse values errors absent fit) =
  tt , mapAll-readable value-readable values fit , map-readable signalError-readable errors
     , map-readable (λ _ → tt) absent , tt
formatResponse-readable (PropertyResponse results) = tt , map-readable propertyResult-readable results , tt
formatResponse-readable Ack = tt , tt
formatResponse-readable (Complete results warnings) =
  tt , map-readable propertyResult-readable results , map-readable warning-readable warnings , tt
formatResponse-readable (DBCResponse json w) = tt , satisfy-map components-readable json w , tt
formatResponse-readable (ValidationResponse issues) = tt , tt , map-readable issue-readable issues , tt
formatResponse-readable (ParsedDBCResponse json w warnings) =
  tt , satisfy-map components-readable json w , map-readable issue-readable warnings , tt
formatResponse-readable (DBCTextResponse _ issues) = tt , tt , map-readable issue-readable issues , tt
