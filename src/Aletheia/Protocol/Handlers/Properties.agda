{-# OPTIONS --safe --without-K #-}

-- Correctness of the SetProperties parse-failure → wire-error routing.
--
-- AGDA-D-10.1 (R23): the LTL-property JSON parser is reason-carrying
-- (`parseProperty : JSON → ParseFail ⊎ _`, fork-free), and `parseFailResponse`
-- (`Protocol.Handlers`) maps each `ParseFail` verdict to the wire error.  That
-- mapping is the one link in the chain that the parser roundtrip proof does NOT
-- reach (it lives in a runtime handler, not the proof tree).  These lemmas pin
-- it, so the kernel→wire-code path is *proven*, not merely type-checked.
--
-- Why a proof and not per-binding tests: the mapping is BINDING-INDEPENDENT —
-- the kernel emits the same JSON for every caller, so proving it once here
-- discharges what a Python / Go / C++ behavior test would each re-verify
-- through its own FFI transport.  The transport itself (the error-envelope
-- round-trip from wire JSON to each binding's typed error) is already covered
-- generically per binding by the existing input-bound / parse-error tests.
--
-- Each lemma is `refl`: `parseFailResponse` pattern-matches the `ParseFail`
-- constructor, so `proj₂ (parseFailResponse …)` reduces definitionally to the
-- expected `Response.Error`, and `errorCode` reduces that error to its wire
-- code string.
module Aletheia.Protocol.Handlers.Properties where

open import Data.Char using (Char)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (proj₂)
open import Data.String using (String; fromList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Aletheia.Error using
  ( WithContext; ParseErr; InvalidIdentifier; HandlerErr
  ; PropertyParseFailed; InputBoundExceeded; errorCode )
open import Aletheia.Limits using (IdentifierLength; max-identifier-length)
open import Aletheia.LTL.JSON using (Shape; BadSignal)
open import Aletheia.DBC.Identifier using (TooLong; BadChars)
open import Aletheia.Protocol.Message using (Response)
open import Aletheia.Protocol.StreamState using (StreamState)
open import Aletheia.Protocol.Handlers using (parseFailResponse)

-- ============================================================================
-- ROUTING — each ParseFail verdict maps to a fixed Response.Error
-- ============================================================================
-- Pinning the full constructor captures every payload (bound kind, observed
-- length, limit, offending name, property index), so any rewiring of the
-- handler mapping breaks these.

-- Malformed JSON shape → untyped handler error carrying the property index.
parseFailResponse-shape : ∀ (st : StreamState) (i : ℕ)
  → proj₂ (parseFailResponse st i Shape)
    ≡ Response.Error (WithContext "SetProperties" (HandlerErr (PropertyParseFailed i)))
parseFailResponse-shape _ _ = refl

-- Over-long signal name → typed InputBoundExceeded carrying the
-- IdentifierLength bound kind, the observed length, and the limit
-- (preserves AGDA-D-32.1's structured triple).
parseFailResponse-tooLong : ∀ (st : StreamState) (i n : ℕ)
  → proj₂ (parseFailResponse st i (BadSignal (TooLong n)))
    ≡ Response.Error (WithContext "SetProperties"
        (InputBoundExceeded IdentifierLength n max-identifier-length))
parseFailResponse-tooLong _ _ _ = refl

-- Bad-charset / empty signal name → typed ParseErr InvalidIdentifier
-- carrying the offending name.
parseFailResponse-badChars : ∀ (st : StreamState) (i : ℕ) (cs : List Char)
  → proj₂ (parseFailResponse st i (BadSignal (BadChars cs)))
    ≡ Response.Error (WithContext "SetProperties" (ParseErr (InvalidIdentifier (fromList cs))))
parseFailResponse-badChars _ _ _ = refl

-- ============================================================================
-- WIRE CODE — the binding-observable `code` string for each signal-name reason
-- ============================================================================
-- These are exactly the assertions the (now-removed) per-binding behavior
-- tests would have made, discharged once kernel-side for all bindings.

responseErrorCode : Response → Maybe String
responseErrorCode (Response.Error e) = just (errorCode e)
responseErrorCode _                  = nothing

-- bad charset / empty → "parse_invalid_identifier"
badChars-wire-code : ∀ (st : StreamState) (i : ℕ) (cs : List Char)
  → responseErrorCode (proj₂ (parseFailResponse st i (BadSignal (BadChars cs))))
    ≡ just "parse_invalid_identifier"
badChars-wire-code _ _ _ = refl

-- over-long → "input_bound_exceeded" (the "identifier_length" bound_kind is
-- carried structurally by the InputBoundExceeded ctor pinned above).
tooLong-wire-code : ∀ (st : StreamState) (i n : ℕ)
  → responseErrorCode (proj₂ (parseFailResponse st i (BadSignal (TooLong n))))
    ≡ just "input_bound_exceeded"
tooLong-wire-code _ _ _ = refl
