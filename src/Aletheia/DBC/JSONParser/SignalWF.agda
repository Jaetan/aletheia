{-# OPTIONS --safe --without-K #-}

-- Signal-level well-formedness proofs for the DBC JSON parser.
--
-- Purpose: Prove that if parseSignalFields/parseSignal succeeds, the result
-- satisfies WellFormedSignal (startBit < 64, bitLength < 65).
-- Key insight: The parser enforces bounds via _%_ (modulo), and m%n<n
-- from Data.Nat.DivMod proves all modular results are in-bounds.
-- Role: Used by MessageWF for the signal-list component.
module Aletheia.DBC.JSONParser.SignalWF where

open import Data.Nat using (ℕ; _+_; _<_)
open import Data.Nat.DivMod using (m%n<n)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.String using (String)
open import Data.Product using (_×_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Aletheia.Protocol.JSON using (JSON; JNull; JBool; JNumber; JString; JArray; JObject;
  lookupString; lookupBool; lookupNat; lookupRational; lookupArray)
open import Aletheia.CAN.Endianness using (ByteOrder)
open import Aletheia.DBC.Types using (DBCSignal; SignalPresence)
open import Aletheia.DBC.JSONParser using (parseSignalFields; parseSignal; parseSignalList;
  parseByteOrder; parseSigned; parseSignalPresence)
open import Aletheia.DBC.Formatter.WellFormed using (WellFormedSignal)

-- ============================================================================
-- SIGNAL FIELDS WELL-FORMEDNESS
-- ============================================================================

-- If parseSignalFields succeeds, the result is well-formed.
-- Strategy: nested with on each lookup/parse step. Failure cases are absurd.
-- In the final success case, startBit = sb % 64 and bitLength = bl % 65,
-- so m%n<n provides the bounds.
parseSignalFields-wf : ∀ ctx name obj sig
  → parseSignalFields ctx name obj ≡ inj₂ sig → WellFormedSignal sig
parseSignalFields-wf ctx name obj sig eq
  with lookupNat "startBit" obj | eq
... | nothing | ()
... | just sb | eq₁
  with lookupNat "length" obj | eq₁
...   | nothing | ()
...   | just bl | eq₂
    with lookupString "byteOrder" obj | eq₂
...     | nothing | ()
...     | just boStr | eq₃
      with parseByteOrder boStr | eq₃
...       | inj₁ _ | ()
...       | inj₂ bo | eq₄
        with parseSigned obj | eq₄
...         | inj₁ _ | ()
...         | inj₂ isSigned | eq₅
          with lookupRational "factor" obj | eq₅
...           | nothing | ()
...           | just factor | eq₆
            with lookupRational "offset" obj | eq₆
...             | nothing | ()
...             | just offset | eq₇
              with lookupRational "minimum" obj | eq₇
...               | nothing | ()
...               | just minimum | eq₈
                with lookupRational "maximum" obj | eq₈
...                 | nothing | ()
...                 | just maximum | eq₉
                  with lookupString "unit" obj | eq₉
...                   | nothing | ()
...                   | just unit | eq₁₀
                    with parseSignalPresence obj | eq₁₀
...                     | inj₁ _ | ()
...                     | inj₂ presence | refl =
                          record { def-wf = record
                            { startBit-bound = m%n<n sb 64
                            ; bitLength-bound = m%n<n bl 65
                            } }

-- ============================================================================
-- SIGNAL WELL-FORMEDNESS
-- ============================================================================

-- If parseSignal succeeds, the result is well-formed.
parseSignal-wf : ∀ ctx obj sig
  → parseSignal ctx obj ≡ inj₂ sig → WellFormedSignal sig
parseSignal-wf ctx obj sig eq
  with lookupString "name" obj | eq
... | nothing | ()
... | just name | eq' = parseSignalFields-wf _ name obj sig eq'

-- ============================================================================
-- SIGNAL LIST WELL-FORMEDNESS
-- ============================================================================

-- If parseSignalList succeeds, all signals are well-formed.
parseSignalList-wf : ∀ ctx jsons idx sigs
  → parseSignalList ctx jsons idx ≡ inj₂ sigs → All WellFormedSignal sigs
parseSignalList-wf ctx [] idx .[] refl = []
parseSignalList-wf ctx (JObject sigObj ∷ rest) idx sigs eq
  with parseSignal ctx sigObj in sig-eq | eq
... | inj₁ _ | ()
... | inj₂ sig | eq₁
  with parseSignalList ctx rest (idx + 1) in rest-eq | eq₁
...   | inj₁ _ | ()
...   | inj₂ sigs' | refl = parseSignal-wf ctx sigObj sig sig-eq ∷
                             parseSignalList-wf ctx rest (idx + 1) sigs' rest-eq
parseSignalList-wf ctx (JNull     ∷ _) idx sigs ()
parseSignalList-wf ctx (JBool _   ∷ _) idx sigs ()
parseSignalList-wf ctx (JNumber _ ∷ _) idx sigs ()
parseSignalList-wf ctx (JString _ ∷ _) idx sigs ()
parseSignalList-wf ctx (JArray _  ∷ _) idx sigs ()
