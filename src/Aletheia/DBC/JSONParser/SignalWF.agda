{-# OPTIONS --safe --without-K #-}

-- Signal-level well-formedness proofs for the DBC JSON parser.
--
-- Purpose: Prove that if parseSignalFields/parseSignal succeeds, the result
-- satisfies WellFormedSignal (startBit < 512, bitLength < 513).
-- Key insight: The parser enforces bounds via _%_ (modulo), and m%n<n
-- from Data.Nat.DivMod proves modular results are in-bounds.
-- For BigEndian, convertStartBit applies physicalBitPos then subtracts,
-- so convertStartBit-wf-bound provides the startBit bound.
-- Role: Used by MessageWF for the signal-list component.
module Aletheia.DBC.JSONParser.SignalWF where

open import Data.Nat using (ℕ; _+_; _*_; _<_; _≤_; _%_; _/_; suc; zero; z≤n; s≤s; _∸_)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Nat.Properties using (≤-trans; m∸n≤m; m≤m+n; *-monoˡ-≤)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.String using (String)
open import Data.Product using (_×_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)

open import Aletheia.Protocol.JSON using (JSON; JNull; JBool; JNumber; JString; JArray; JObject;
  lookupString; lookupBool; lookupNat; lookupRational; lookupArray)
open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian; convertStartBit)
open import Aletheia.CAN.Endianness.Properties using (convertStartBit-wf-bound)
open import Aletheia.DBC.Types using (DBCSignal; SignalPresence)
open import Aletheia.DBC.JSONParser using (parseSignalFields; parseSignal; parseSignalList;
  parseByteOrder; parseSigned; parseSignalPresence)
open import Aletheia.DBC.Formatter.WellFormed using (WellFormedSignal)

-- ============================================================================
-- HELPER: convertStartBit bound for parser well-formedness
-- ============================================================================

private
  -- 0 ∸ n ≡ 0 for any n. Needed because BUILTIN NATMINUS doesn't reduce
  -- when the second argument is a stuck expression (like s / 8).
  0∸n≡0 : ∀ n → 0 ∸ n ≡ 0
  0∸n≡0 zero    = refl
  0∸n≡0 (suc _) = refl

  -- convertStartBit produces < 512 for valid frame byte counts (≤ 64).
  -- LE case: identity, so s < 512 suffices.
  -- BE case (zero): physicalBitPos 0 BE s = (0 ∸ (s/8))*8 + s%8; rewrite stuck
  --   subtraction via 0∸n≡0 to get s%8 ∸ (l∸1) < 8 ≤ 512.
  -- BE case (suc n): uses generic convertStartBit-wf-bound.
  convertSB-bound : ∀ n bo s l → n ≤ 64 → s < 512 → convertStartBit n bo s l < 512
  convertSB-bound _ LittleEndian s _ _ s<512 = s<512
  convertSB-bound zero BigEndian s l _ _ = subst (_< 512) (sym eq) bound
    where
      eq : convertStartBit 0 BigEndian s l ≡ s % 8 ∸ (l ∸ 1)
      eq = cong (_∸ (l ∸ 1)) (cong (λ x → x * 8 + s % 8) (0∸n≡0 (s / 8)))
      bound : s % 8 ∸ (l ∸ 1) < 512
      bound = ≤-trans (≤-trans (s≤s (m∸n≤m (s % 8) (l ∸ 1))) (m%n<n s 8)) (m≤m+n 8 504)
  convertSB-bound (suc n) BigEndian s l n≤64 s<512 =
    convertStartBit-wf-bound (suc n) BigEndian s l (s≤s z≤n) (*-monoˡ-≤ 8 n≤64) s<512

-- ============================================================================
-- SIGNAL FIELDS WELL-FORMEDNESS
-- ============================================================================

-- If parseSignalFields succeeds, the result is well-formed.
-- Strategy: nested with on each lookup/parse step. Failure cases are absurd.
-- In the final success case, startBit = sb % 512 and bitLength = bl % 513,
-- so m%n<n provides the bounds. For BE, convertSB-bound handles startBit.
parseSignalFields-wf : ∀ frameBytes ctx name obj sig
  → frameBytes ≤ 64
  → parseSignalFields frameBytes ctx name obj ≡ inj₂ sig → WellFormedSignal sig
parseSignalFields-wf frameBytes ctx name obj sig fb≤64 eq
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
                            { startBit-bound = convertSB-bound frameBytes bo (sb % 512) (bl % 513) fb≤64 (m%n<n sb 512)
                            ; bitLength-bound = m%n<n bl 513
                            } }

-- ============================================================================
-- SIGNAL WELL-FORMEDNESS
-- ============================================================================

-- If parseSignal succeeds, the result is well-formed.
parseSignal-wf : ∀ frameBytes ctx obj sig
  → frameBytes ≤ 64
  → parseSignal frameBytes ctx obj ≡ inj₂ sig → WellFormedSignal sig
parseSignal-wf frameBytes ctx obj sig fb≤64 eq
  with lookupString "name" obj | eq
... | nothing | ()
... | just name | eq' = parseSignalFields-wf frameBytes _ name obj sig fb≤64 eq'

-- ============================================================================
-- SIGNAL LIST WELL-FORMEDNESS
-- ============================================================================

-- If parseSignalList succeeds, all signals are well-formed.
parseSignalList-wf : ∀ frameBytes ctx jsons idx sigs
  → frameBytes ≤ 64
  → parseSignalList frameBytes ctx jsons idx ≡ inj₂ sigs → All WellFormedSignal sigs
parseSignalList-wf frameBytes ctx [] idx .[] fb≤64 refl = []
parseSignalList-wf frameBytes ctx (JObject sigObj ∷ rest) idx sigs fb≤64 eq
  with parseSignal frameBytes ctx sigObj in sig-eq | eq
... | inj₁ _ | ()
... | inj₂ sig | eq₁
  with parseSignalList frameBytes ctx rest (idx + 1) in rest-eq | eq₁
...   | inj₁ _ | ()
...   | inj₂ sigs' | refl = parseSignal-wf frameBytes ctx sigObj sig fb≤64 sig-eq ∷
                             parseSignalList-wf frameBytes ctx rest (idx + 1) sigs' fb≤64 rest-eq
parseSignalList-wf frameBytes ctx (JNull     ∷ _) idx sigs fb≤64 ()
parseSignalList-wf frameBytes ctx (JBool _   ∷ _) idx sigs fb≤64 ()
parseSignalList-wf frameBytes ctx (JNumber _ ∷ _) idx sigs fb≤64 ()
parseSignalList-wf frameBytes ctx (JString _ ∷ _) idx sigs fb≤64 ()
parseSignalList-wf frameBytes ctx (JArray _  ∷ _) idx sigs fb≤64 ()
