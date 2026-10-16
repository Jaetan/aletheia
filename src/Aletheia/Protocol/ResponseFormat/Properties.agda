-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Correctness properties for response formatting.
--
-- Purpose: Prove format-response injectivity (Ack uniqueness), and that an
-- error reply's `observed` never passes `observed-ceiling`.
-- Risk mitigated: Ack formatted as Violation or vice versa would cause
-- language bindings to misinterpret the result; a bound refusal echoing a
-- measured value of unbounded length would cost the host process its heap
-- while the reply is rendered, and pass the range bindings decode it into.
module Aletheia.Protocol.ResponseFormat.Properties where

open import Data.Bool using (true; false; T)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Nat using (_≤_; _<_; _<ᵇ_; _^_; _∸_)
open import Data.Nat.Properties using (<ᵇ⇒<; <⇒<ᵇ; ≤⇒≯; ≮⇒≥; ≤-refl)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.String using (String) renaming (_++_ to _++ₛ_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

import Aletheia.Error as Err
open import Aletheia.Error using (showObserved)
open import Aletheia.Limits using (boundKindCode; boundKindLabel; observed-ceiling; saturateObserved)
open import Aletheia.Prelude using (ℕtoℚ)
open import Aletheia.Protocol.JSON.Types using (JSON; JObject; JStringS; JNumber)
open import Aletheia.Protocol.Message using (Success; Error;
  ExtractionResultsResponse; PropertyResponse; Ack; Complete; ValidationResponse; DBCResponse;
  ParsedDBCResponse; DBCTextResponse)
open import Aletheia.Protocol.Response using ()
open import Aletheia.Protocol.ResponseFormat using (formatResponse; errorExtras)

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
formatResponse-ack-unique (ExtractionResultsResponse _ _ _) ()
-- PropertyResponse carries `List PropertyResult`.
-- The wire emit is `{"type": "property_batch", "results": [...]}` —
-- always a 2-field JObject regardless of list length, so the inhabitant
-- can never collapse to Ack's 1-field shape.  The single `_` covers the
-- empty / singleton / batch cases uniformly.
formatResponse-ack-unique (PropertyResponse _) ()
formatResponse-ack-unique Ack _ = refl
formatResponse-ack-unique (Complete _ _) ()
formatResponse-ack-unique (DBCResponse _) ()
formatResponse-ack-unique (ValidationResponse _) ()
formatResponse-ack-unique (ParsedDBCResponse _ _) ()
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
-- and its fields write it through `saturateObserved`; the `At` form delegates
-- to both and adds `field`.
formatError-bound : ∀ k o l → Err.formatError (Err.InputBoundExceeded k o l) ≡
  boundKindLabel k ++ₛ " " ++ₛ showObserved o ++ₛ " exceeds limit " ++ₛ showℕ l
formatError-bound _ _ _ = refl

errorExtras-bound : ∀ k o l → errorExtras (Err.InputBoundExceeded k o l) ≡
  ("bound_kind" , JStringS (boundKindCode k)) ∷
  ("observed"   , JNumber (ℕtoℚ (saturateObserved o))) ∷
  ("limit"      , JNumber (ℕtoℚ l)) ∷ []
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
