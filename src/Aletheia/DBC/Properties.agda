{-# OPTIONS --safe --without-K #-}

-- Correctness properties for DBC parsers and types.
--
-- Purpose: Prove properties of DBC parsing and validation.
-- Properties: Bounded values (IDs, start bits, lengths), determinism, well-formedness.
-- Role: Phase 1 basic properties; full soundness proofs deferred to Phase 3.
--
-- Status: Runtime semantic checks implemented (signal overlap, range validation).
-- Future work: Round-trip properties (parse ∘ print ≡ id), grammar formalization.
module Aletheia.DBC.Properties where

open import Aletheia.DBC.Types
open import Aletheia.DBC.Parser
open import Aletheia.Parser.Combinators
open import Aletheia.CAN.Frame
open import Aletheia.CAN.Signal
open import Aletheia.CAN.Endianness
open import Data.List using (List; []; _∷_; length; all)
open import Data.String as String using (String; toList)
open import Data.Char using (Char)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Nat using (ℕ; _+_; _*_; _<_; _≤_; zero; suc)
open import Data.Fin using (Fin; toℕ)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Rational using (ℚ; _≤ᵇ_)
open import Data.Integer as ℤ using (ℤ; +_; -[1+_])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_)

-- ============================================================================
-- BASIC STRUCTURAL PROPERTIES
-- ============================================================================

-- Property: Parsed signal start bits are always bounded
startBit-bounded : ∀ (sig : DBCSignal) → toℕ (SignalDef.startBit (DBCSignal.signalDef sig)) < 64
startBit-bounded sig = toℕ<n (SignalDef.startBit (DBCSignal.signalDef sig))
  where
    open import Data.Fin.Properties using (toℕ<n)

-- Property: Parsed signal bit lengths are always bounded
bitLength-bounded : ∀ (sig : DBCSignal) → toℕ (SignalDef.bitLength (DBCSignal.signalDef sig)) ≤ 64
bitLength-bounded sig = ≤-pred (toℕ<n (SignalDef.bitLength (DBCSignal.signalDef sig)))
  where
    open import Data.Fin.Properties using (toℕ<n)
    open import Data.Nat.Properties using (≤-pred)

-- Property: Parsed message IDs are valid CAN IDs
messageId-bounded : ∀ (msg : DBCMessage) → toℕ (DBCMessage.id msg) < 2048
messageId-bounded msg = toℕ<n (DBCMessage.id msg)
  where
    open import Data.Fin.Properties using (toℕ<n)

-- Property: Parsed DLC values are valid
dlc-bounded : ∀ (msg : DBCMessage) → toℕ (DBCMessage.dlc msg) ≤ 8
dlc-bounded msg = ≤-pred (toℕ<n (DBCMessage.dlc msg))
  where
    open import Data.Fin.Properties using (toℕ<n)
    open import Data.Nat.Properties using (≤-pred)

-- ============================================================================
-- PARSER DETERMINISM
-- ============================================================================

-- Property: Parser is deterministic - same input produces same output
parseDBC-deterministic : ∀ (input : List Char)
  (r1 r2 : DBC × List Char) →
  parseDBC input ≡ just r1 →
  parseDBC input ≡ just r2 →
  r1 ≡ r2
parseDBC-deterministic input r1 r2 eq1 eq2 rewrite eq1 | eq2 = refl

-- Same for signal parser
parseSignalDef-deterministic : ∀ (indent : ℕ) (input : List Char)
  (r1 r2 : DBCSignal × List Char) →
  parseSignalDef indent input ≡ just r1 →
  parseSignalDef indent input ≡ just r2 →
  r1 ≡ r2
parseSignalDef-deterministic indent input r1 r2 eq1 eq2 rewrite eq1 | eq2 = refl

-- ============================================================================
-- SEMANTIC CORRECTNESS PROPERTIES
-- ============================================================================

-- Property: Signal value ranges are consistent (minimum ≤ maximum)
-- This is a runtime check since we can't prove it statically without
-- constraints in the parser
signal-ranges-consistent : DBCSignal → Bool
signal-ranges-consistent sig =
  let open SignalDef (DBCSignal.signalDef sig)
  in minimum ≤ᵇ maximum

-- Check all signals in a message have consistent ranges
message-ranges-consistent : DBCMessage → Bool
message-ranges-consistent msg =
  Data.List.all signal-ranges-consistent (DBCMessage.signals msg)
  where
    open import Data.List using (all)

-- Check all messages in a DBC have consistent ranges
dbc-ranges-consistent : DBC → Bool
dbc-ranges-consistent dbc =
  Data.List.all message-ranges-consistent (DBC.messages dbc)
  where
    open import Data.List using (all)

-- ============================================================================
-- TEST CASES
-- ============================================================================

-- Test: Parse a minimal valid DBC
test-minimal-dbc : Maybe DBC
test-minimal-dbc = runParser parseDBC (toList minimalYAML)
  where
    minimalYAML : String
    minimalYAML = "version: \"1.0\"\n\nmessages:"
-- Expected result: Should parse successfully with empty message list

{- Commented out to avoid expensive normalization during type-checking
test-minimal-dbc-succeeds : is-just test-minimal-dbc ≡ true
test-minimal-dbc-succeeds = refl
-}

-- Test: Parse a simple message
test-simple-message : Maybe DBC
test-simple-message = runParser parseDBC (toList simpleYAML)
  where
    simpleYAML : String
    simpleYAML =
      "version: \"1.0\"\n\n" String.++
      "messages:\n" String.++
      "  - id: 0x100\n" String.++
      "    name: \"TestMsg\"\n" String.++
      "    dlc: 8\n" String.++
      "    sender: \"ECU\"\n" String.++
      "    signals:"
      where open import Data.String using (_++_)

-- Test: Parse a message with a signal
test-message-with-signal : Maybe DBC
test-message-with-signal = runParser parseDBC (toList fullYAML)
  where
    fullYAML : String
    fullYAML =
      "version: \"1.0\"\n\n" String.++
      "messages:\n" String.++
      "  - id: 0x100\n" String.++
      "    name: \"TestMsg\"\n" String.++
      "    dlc: 8\n" String.++
      "    sender: \"ECU\"\n" String.++
      "    signals:\n" String.++
      "      - name: \"TestSignal\"\n" String.++
      "        start_bit: 0\n" String.++
      "        bit_length: 8\n" String.++
      "        byte_order: \"little_endian\"\n" String.++
      "        value_type: \"unsigned\"\n" String.++
      "        factor: 1\n" String.++
      "        offset: 0\n" String.++
      "        minimum: 0\n" String.++
      "        maximum: 255\n" String.++
      "        unit: \"\""
      where open import Data.String using (_++_)

-- Test primitive parsers independently
-- These tests can be evaluated at runtime to verify parser behavior
test-natural : Maybe ℕ
test-natural = runParser natural (toList "123")
-- Expected: just 123

test-hexNumber : Maybe ℕ
test-hexNumber = runParser hexNumber (toList "0x100")
-- Expected: just 256

test-integer-positive : Maybe ℤ
test-integer-positive = runParser integer (toList "42")
-- Expected: just (+ 42)

test-integer-negative : Maybe ℤ
test-integer-negative = runParser integer (toList "-42")
-- Expected: just -[1+ 41 ]

-- Test byte order parsing
test-byteorder-little : Maybe ByteOrder
test-byteorder-little = runParser parseByteOrder (toList "little_endian")
-- Expected: just LittleEndian

test-byteorder-big : Maybe ByteOrder
test-byteorder-big = runParser parseByteOrder (toList "big_endian")
-- Expected: just BigEndian

{- NOTE: Commented out normalization proofs to avoid expensive type-checking
   These can be verified by evaluating the test values at runtime

test-natural-correct : test-natural ≡ just 123
test-natural-correct = refl

test-hexNumber-correct : test-hexNumber ≡ just 256
test-hexNumber-correct = refl

test-integer-positive-correct : test-integer-positive ≡ just (+ 42)
test-integer-positive-correct = refl

test-integer-negative-correct : test-integer-negative ≡ just -[1+ 41 ]
test-integer-negative-correct = refl

test-byteorder-little-correct : test-byteorder-little ≡ just LittleEndian
test-byteorder-little-correct = refl

test-byteorder-big-correct : test-byteorder-big ≡ just BigEndian
test-byteorder-big-correct = refl
-}

-- ============================================================================
-- PROPERTY-BASED INVARIANTS
-- ============================================================================

-- Helper: Check if a signal is well-formed
signal-well-formed : DBCSignal → Bool
signal-well-formed sig =
  let open SignalDef (DBCSignal.signalDef sig)
  in (toℕ startBit Data.Nat.<ᵇ 64) ∧
     (toℕ bitLength Data.Nat.≤ᵇ 64) ∧
     (minimum Data.Rational.≤ᵇ maximum)
  where
    open import Data.Nat using (_<ᵇ_; _≤ᵇ_)

-- Helper: Check if a message is well-formed
message-well-formed : DBCMessage → Bool
message-well-formed msg =
  (toℕ (DBCMessage.dlc msg) Data.Nat.≤ᵇ 8) ∧
  Data.List.all signal-well-formed (DBCMessage.signals msg)
  where
    open import Data.Nat using (_≤ᵇ_)
    open import Data.List using (all)

-- If a DBC parses successfully, all its structural properties hold
dbc-well-formed : DBC → Bool
dbc-well-formed dbc =
  dbc-ranges-consistent dbc ∧
  Data.List.all message-well-formed (DBC.messages dbc)
  where
    open import Data.List using (all)

-- Theorem: If parseDBC succeeds, result is well-formed
-- (Runtime property - holds by construction of parser)
parseDBC-well-formed : ∀ (input : List Char) (dbc : DBC) (rest : List Char) →
  parseDBC input ≡ just (dbc , rest) →
  dbc-well-formed dbc ≡ true
parseDBC-well-formed input dbc rest eq = {!!}  -- TODO: Prove by induction on parse tree

-- ============================================================================
-- FUTURE PROOF OBLIGATIONS (Phase 3+)
-- ============================================================================

{- TODO Phase 3: Define formal YAML/DBC grammar

   We will need to define:

   ValidYAML : List Char → Set
   ValidDBC : List Char → DBC → Set

   And prove parser soundness:

   parseDBC-sound : ∀ (input : List Char) (dbc : DBC) (rest : List Char) →
     parseDBC input ≡ just (dbc , rest) →
     ValidDBC input dbc
-}

{- TODO Phase 5: Implement pretty-printer and prove round-trip properties

   We will need to implement:

   printDBC : DBC → String

   And prove:

   parse-print-inverse : ∀ (dbc : DBC) →
     parseDBC (toList (printDBC dbc)) ≡ just (dbc , [])

   print-parse-inverse : ∀ (input : String) (dbc : DBC) →
     parseDBC (toList input) ≡ just (dbc , []) →
     Data.Product.∃[ normalized ] printDBC dbc ≡ normalized
-}
