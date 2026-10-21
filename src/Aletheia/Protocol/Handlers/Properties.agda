-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Correctness of the SetProperties parse-failure → wire-error routing.
--
-- The LTL-property JSON parser is reason-carrying
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

open import Data.Char using (Char; toℕ)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (proj₂)
open import Data.String using (String; fromList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Aletheia.Error using
  ( WithContext; ParseErr; InvalidIdentifier; HandlerErr; InvalidCharacter; InField
  ; PropertyParseFailed; UnknownSignal; KeywordName; InPart; InputBoundExceededAt; errorCode )
open import Aletheia.Limits using (IdentifierLength; max-identifier-length)
open import Aletheia.LTL.JSON using (Shape; BadSignal; UnknownSignalName)
open import Aletheia.DBC.JSONParser using (IdentRefusal; NotAscii; NotIdentifier; TooLong; Keyword; identError)
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

-- A refused signal name → the error a parsed DBC's name gets, read from
-- the `signal` slot: one decision and one spelling on both routes.
parseFailResponse-badSignal : ∀ (st : StreamState) (i : ℕ) (cs : List Char) (r : IdentRefusal)
  → proj₂ (parseFailResponse st i (BadSignal cs r))
    ≡ Response.Error (WithContext "SetProperties" (identError "signal" cs r))
parseFailResponse-badSignal _ _ _ _ = refl

-- Not an identifier → typed ParseErr InvalidIdentifier carrying the name.
parseFailResponse-notIdentifier : ∀ (st : StreamState) (i : ℕ) (cs : List Char)
  → proj₂ (parseFailResponse st i (BadSignal cs NotIdentifier))
    ≡ Response.Error (WithContext "SetProperties" (ParseErr (InvalidIdentifier (InPart "signal") (fromList cs))))
parseFailResponse-notIdentifier _ _ _ = refl

-- A character outside ASCII → the typed character refusal, indexed in the slot.
parseFailResponse-notAscii : ∀ (st : StreamState) (i : ℕ) (cs : List Char) (k : ℕ) (c : Char)
  → proj₂ (parseFailResponse st i (BadSignal cs (NotAscii k c)))
    ≡ Response.Error (WithContext "SetProperties" (InvalidCharacter (InField "signal" k) (toℕ c)))
parseFailResponse-notAscii _ _ _ _ _ = refl

-- ============================================================================
-- WIRE CODE — the binding-observable `code` string for each signal-name reason
-- ============================================================================
-- These are exactly the assertions the (now-removed) per-binding behavior
-- tests would have made, discharged once kernel-side for all bindings.

responseErrorCode : Response → Maybe String
responseErrorCode (Response.Error e) = just (errorCode e)
responseErrorCode _                  = nothing

-- not an identifier → "parse_invalid_identifier"
notIdentifier-wire-code : ∀ (st : StreamState) (i : ℕ) (cs : List Char)
  → responseErrorCode (proj₂ (parseFailResponse st i (BadSignal cs NotIdentifier)))
    ≡ just "parse_invalid_identifier"
notIdentifier-wire-code _ _ _ = refl

-- a character outside ASCII → "dbc_invalid_character"
notAscii-wire-code : ∀ (st : StreamState) (i : ℕ) (cs : List Char) (k : ℕ) (c : Char)
  → responseErrorCode (proj₂ (parseFailResponse st i (BadSignal cs (NotAscii k c))))
    ≡ just "dbc_invalid_character"
notAscii-wire-code _ _ _ _ _ = refl

-- A name past the identifier bound → the typed bound refusal carrying the
-- slot, the kind, the observed length and the limit.
parseFailResponse-tooLong : ∀ (st : StreamState) (i n : ℕ) (cs : List Char)
  → proj₂ (parseFailResponse st i (BadSignal cs (TooLong n)))
    ≡ Response.Error (WithContext "SetProperties"
        (InputBoundExceededAt (InPart "signal") IdentifierLength n max-identifier-length))
parseFailResponse-tooLong _ _ _ _ = refl

tooLong-wire-code : ∀ (st : StreamState) (i n : ℕ) (cs : List Char)
  → responseErrorCode (proj₂ (parseFailResponse st i (BadSignal cs (TooLong n))))
    ≡ just "input_bound_exceeded"
tooLong-wire-code _ _ _ _ = refl

-- A keyword as a signal name → the typed keyword refusal naming the slot.
parseFailResponse-keyword : ∀ (st : StreamState) (i : ℕ) (cs kw : List Char)
  → proj₂ (parseFailResponse st i (BadSignal cs (Keyword kw)))
    ≡ Response.Error (WithContext "SetProperties" (KeywordName (InPart "signal") (fromList kw)))
parseFailResponse-keyword _ _ _ _ = refl

keyword-wire-code : ∀ (st : StreamState) (i : ℕ) (cs kw : List Char)
  → responseErrorCode (proj₂ (parseFailResponse st i (BadSignal cs (Keyword kw))))
    ≡ just "dbc_keyword_name"
keyword-wire-code _ _ _ _ = refl

-- A name no signal of the DBC carries → the typed handler refusal naming it.
parseFailResponse-unknownSignal : ∀ (st : StreamState) (i : ℕ) (cs : List Char)
  → proj₂ (parseFailResponse st i (UnknownSignalName cs))
    ≡ Response.Error (WithContext "SetProperties" (HandlerErr (UnknownSignal (fromList cs))))
parseFailResponse-unknownSignal _ _ _ = refl

unknownSignal-wire-code : ∀ (st : StreamState) (i : ℕ) (cs : List Char)
  → responseErrorCode (proj₂ (parseFailResponse st i (UnknownSignalName cs)))
    ≡ just "handler_unknown_signal"
unknownSignal-wire-code _ _ _ = refl
