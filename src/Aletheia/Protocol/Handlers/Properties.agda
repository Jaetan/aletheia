-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Correctness of the SetProperties parse-failure → wire-error routing.
--
-- The LTL-property JSON parser is reason-carrying
-- (`parseProperty : JSON → ParseFail ⊎ _`, fork-free), and `parseFailError`
-- (`Protocol.Handlers`) maps each `ParseFail` verdict to the wire error, on
-- set_properties (the reason placed after the property's index) and in the
-- build-time property check (the reason alone) alike.  That
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
-- Each lemma is `refl`: `parseFailError` pattern-matches the `ParseFail`
-- constructor, so it reduces definitionally to the expected error, and
-- `errorCode` reduces that error to its wire code string.
module Aletheia.Protocol.Handlers.Properties where

open import Data.Char using (Char; toℕ)
open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Data.String using (fromList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Aletheia.Error using
  ( ParseErr; InvalidIdentifier; HandlerErr; InvalidCharacter; InField
  ; PropertyParseFailed; PropertyRefused; PropertyRefusal
  ; UnknownSignal; KeywordName; InPart; InputBoundExceededAt; errorCode )
open import Aletheia.Limits using
  (IdentifierLength; max-identifier-length; RationalComponentMagnitude; max-time-bound)
open import Aletheia.LTL.JSON using (Refused; BadSignal; UnknownSignalName; TimeBoundPast; parseFailError)
open import Aletheia.DBC.JSONParser using (IdentRefusal; NotAscii; NotIdentifier; TooLong; Keyword; identError)

-- ============================================================================
-- ROUTING: each ParseFail verdict maps to a fixed error
-- ============================================================================
-- Pinning the full constructor captures every payload (bound kind, observed
-- length, limit, offending name, property index), so any rewiring of the
-- handler mapping breaks these.

-- JSON that is no property → the handler error carrying the reason, placed
-- after the property's index on set_properties and alone in the check.
parseFailError-refused : ∀ (i : ℕ) (r : PropertyRefusal)
  → parseFailError (PropertyParseFailed i) (Refused r) ≡ HandlerErr (PropertyParseFailed i r)
parseFailError-refused _ _ = refl

parseFailError-refused-alone : ∀ (r : PropertyRefusal)
  → parseFailError PropertyRefused (Refused r) ≡ HandlerErr (PropertyRefused r)
parseFailError-refused-alone _ = refl

refused-wire-code : ∀ (i : ℕ) (r : PropertyRefusal)
  → errorCode (parseFailError (PropertyParseFailed i) (Refused r)) ≡ "handler_property_parse_failed"
refused-wire-code _ _ = refl

refused-alone-wire-code : ∀ (r : PropertyRefusal)
  → errorCode (parseFailError PropertyRefused (Refused r)) ≡ "handler_property_parse_failed"
refused-alone-wire-code _ = refl

-- A time bound past its limit → the bound refusal naming the time bound.
parseFailError-timeBound : ∀ (i n : ℕ)
  → parseFailError (PropertyParseFailed i) (TimeBoundPast n)
    ≡ InputBoundExceededAt (InPart "time bound") RationalComponentMagnitude n max-time-bound
parseFailError-timeBound _ _ = refl

timeBound-wire-code : ∀ (i n : ℕ)
  → errorCode (parseFailError (PropertyParseFailed i) (TimeBoundPast n)) ≡ "input_bound_exceeded"
timeBound-wire-code _ _ = refl

-- A refused signal name → the error a parsed DBC's name gets, read from
-- the `signal` slot: one decision and one spelling on both routes.
parseFailError-badSignal : ∀ (i : ℕ) (cs : List Char) (r : IdentRefusal)
  → parseFailError (PropertyParseFailed i) (BadSignal cs r)
    ≡ identError "signal" cs r
parseFailError-badSignal _ _ _ = refl

-- Not an identifier → typed ParseErr InvalidIdentifier carrying the name.
parseFailError-notIdentifier : ∀ (i : ℕ) (cs : List Char)
  → parseFailError (PropertyParseFailed i) (BadSignal cs NotIdentifier)
    ≡ ParseErr (InvalidIdentifier (InPart "signal") (fromList cs))
parseFailError-notIdentifier _ _ = refl

-- A character outside ASCII → the typed character refusal, indexed in the slot.
parseFailError-notAscii : ∀ (i : ℕ) (cs : List Char) (k : ℕ) (c : Char)
  → parseFailError (PropertyParseFailed i) (BadSignal cs (NotAscii k c))
    ≡ InvalidCharacter (InField "signal" k) (toℕ c)
parseFailError-notAscii _ _ _ _ = refl

-- ============================================================================
-- WIRE CODE — the binding-observable `code` string for each signal-name reason
-- ============================================================================
-- These are exactly the assertions the (now-removed) per-binding behavior
-- tests would have made, discharged once kernel-side for all bindings.

-- not an identifier → "parse_invalid_identifier"
notIdentifier-wire-code : ∀ (i : ℕ) (cs : List Char)
  → errorCode (parseFailError (PropertyParseFailed i) (BadSignal cs NotIdentifier))
    ≡ "parse_invalid_identifier"
notIdentifier-wire-code _ _ = refl

-- a character outside ASCII → "dbc_invalid_character"
notAscii-wire-code : ∀ (i : ℕ) (cs : List Char) (k : ℕ) (c : Char)
  → errorCode (parseFailError (PropertyParseFailed i) (BadSignal cs (NotAscii k c)))
    ≡ "dbc_invalid_character"
notAscii-wire-code _ _ _ _ = refl

-- A name past the identifier bound → the typed bound refusal carrying the
-- slot, the kind, the observed length and the limit.
parseFailError-tooLong : ∀ (i n : ℕ) (cs : List Char)
  → parseFailError (PropertyParseFailed i) (BadSignal cs (TooLong n))
    ≡ InputBoundExceededAt (InPart "signal") IdentifierLength n max-identifier-length
parseFailError-tooLong _ _ _ = refl

tooLong-wire-code : ∀ (i n : ℕ) (cs : List Char)
  → errorCode (parseFailError (PropertyParseFailed i) (BadSignal cs (TooLong n)))
    ≡ "input_bound_exceeded"
tooLong-wire-code _ _ _ = refl

-- A keyword as a signal name → the typed keyword refusal naming the slot.
parseFailError-keyword : ∀ (i : ℕ) (cs kw : List Char)
  → parseFailError (PropertyParseFailed i) (BadSignal cs (Keyword kw))
    ≡ KeywordName (InPart "signal") (fromList kw)
parseFailError-keyword _ _ _ = refl

keyword-wire-code : ∀ (i : ℕ) (cs kw : List Char)
  → errorCode (parseFailError (PropertyParseFailed i) (BadSignal cs (Keyword kw)))
    ≡ "dbc_keyword_name"
keyword-wire-code _ _ _ = refl

-- A name no signal of the DBC carries → the typed handler refusal naming it.
parseFailError-unknownSignal : ∀ (i : ℕ) (cs : List Char)
  → parseFailError (PropertyParseFailed i) (UnknownSignalName cs)
    ≡ HandlerErr (UnknownSignal (fromList cs))
parseFailError-unknownSignal _ _ = refl

unknownSignal-wire-code : ∀ (i : ℕ) (cs : List Char)
  → errorCode (parseFailError (PropertyParseFailed i) (UnknownSignalName cs))
    ≡ "handler_unknown_signal"
unknownSignal-wire-code _ _ = refl
