{-# OPTIONS --safe --without-K #-}

-- Signal-level well-formedness proofs for the DBC JSON parser.
--
-- Purpose: Prove that if parseSignalFields/parseSignal succeeds, the result
-- satisfies WellFormedSignal (startBit < max-physical-bits, bitLength < suc max-physical-bits).
-- Key insight: The parser enforces bounds via _%_ (modulo), and m%n<n
-- from Data.Nat.DivMod proves modular results are in-bounds.
-- For BigEndian, convertStartBit applies physicalBitPos then subtracts,
-- so convertStartBit-wf-bound provides the startBit bound.
-- Role: Used by MessageWF for the signal-list component.
module Aletheia.DBC.JSONParser.SignalWF where
open import Aletheia.DBC.Identifier using (Identifier)

open import Data.Nat using (ℕ; _+_; _*_; _<_; _≤_; _%_; _/_; _≤ᵇ_; _<ᵇ_; suc; zero; z≤n; s≤s; _∸_)
open import Data.Nat.DivMod using (m%n<n)
open import Data.Nat.Properties using (≤-trans; m∸n≤m; *-monoˡ-≤; ≤ᵇ⇒≤; <ᵇ⇒<)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.String using (String)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; T)
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)

open import Data.Char using (Char)

open import Aletheia.JSON using (JSON; JNull; JBool; JNumber; JString; JArray; JObject;
  lookupString; lookupChars; lookupBool; lookupNat; lookupRational; lookupArray)
open import Aletheia.CAN.Endianness using (ByteOrder; LittleEndian; BigEndian; convertStartBit)
open import Aletheia.CAN.Endianness.Properties using (convertStartBit-wf-bound)
open import Aletheia.DBC.Types using (DBCSignal; SignalPresence)
open import Aletheia.DBC.JSONParser using (parseSignalFields; parseSignal; parseSignalList; lookupDecRat;
  parseByteOrder; parseSigned; parseSignalPresence; addSignalContext; physicalGate; validateIdent; validateIdentList;
  parseOptionalArray; parseCharsList)
open import Aletheia.DBC.Formatter.WellFormed using (WellFormedSignal;
  PhysicallyValid; pv-LE; pv-BE)
open import Aletheia.CAN.Constants using (max-physical-bits; 8≤max-physical-bits)

-- ============================================================================
-- HELPER: convertStartBit bound for parser well-formedness
-- ============================================================================

private
  -- 0 ∸ n ≡ 0 for any n. Needed because BUILTIN NATMINUS doesn't reduce
  -- when the second argument is a stuck expression (like s / 8).
  0∸n≡0 : ∀ n → 0 ∸ n ≡ 0
  0∸n≡0 zero    = refl
  0∸n≡0 (suc _) = refl

  -- convertStartBit produces < max-physical-bits for valid frame byte counts (≤ 64).
  -- LE case: identity, so s < max-physical-bits suffices.
  -- BE case (zero): physicalBitPos 0 BE s = (0 ∸ (s/8))*8 + s%8; rewrite stuck
  --   subtraction via 0∸n≡0 to get s%8 ∸ (l∸1) < 8 ≤ max-physical-bits.
  -- BE case (suc n): uses generic convertStartBit-wf-bound.
  convertSB-bound : ∀ n bo s l → n ≤ 64 → s < max-physical-bits → convertStartBit n bo s l < max-physical-bits
  convertSB-bound _ LittleEndian s _ _ s<mpb = s<mpb
  convertSB-bound zero BigEndian s l _ _ = subst (_< max-physical-bits) (sym eq) bound
    where
      eq : convertStartBit 0 BigEndian s l ≡ s % 8 ∸ (l ∸ 1)
      eq = cong (_∸ (l ∸ 1)) (cong (λ x → x * 8 + s % 8) (0∸n≡0 (s / 8)))
      bound : s % 8 ∸ (l ∸ 1) < max-physical-bits
      bound = ≤-trans (≤-trans (s≤s (m∸n≤m (s % 8) (l ∸ 1))) (m%n<n s 8)) 8≤max-physical-bits
  convertSB-bound (suc n) BigEndian s l n≤64 s<mpb =
    convertStartBit-wf-bound (suc n) BigEndian s l (s≤s z≤n) (*-monoˡ-≤ 8 n≤64) s<mpb

  -- Combined helper extracting BOTH WellFormedSignal AND PhysicallyValid in a
  -- single pass after the 11-deep with-chain. Takes byte order as an explicit
  -- parameter so we can pattern-match: LE makes physicalGate reduce to inj₂ rec
  -- immediately; BE forces a 3-deep with-chain on the boolean checks.
  -- Combining eliminates the duplicate postPresence-wf/postPresence-pv pair.
  postPresence-wf×pv :
    ∀ (frameBytes : ℕ) (ctx : String) (name : Identifier) (bo : ByteOrder)
      (sb-mod : ℕ) (sb-bound : sb-mod < max-physical-bits)
      (bl-mod : ℕ) (bl-bound : bl-mod < suc max-physical-bits)
      isSigned factor offset minimum maximum unit presence receivers sig
    → frameBytes ≤ 64
    → addSignalContext ctx (physicalGate frameBytes bo
        (convertStartBit frameBytes bo sb-mod bl-mod)
        bl-mod
        (record
          { name = name
          ; signalDef = record
              { startBit = convertStartBit frameBytes bo sb-mod bl-mod
              ; bitLength = bl-mod
              ; isSigned = isSigned
              ; factor = factor
              ; offset = offset
              ; minimum = minimum
              ; maximum = maximum
              }
          ; byteOrder = bo
          ; unit = unit
          ; presence = presence
          ; receivers = receivers
          }))
      ≡ inj₂ sig
    → WellFormedSignal sig × PhysicallyValid frameBytes sig
  postPresence-wf×pv frameBytes ctx name LittleEndian sb-mod sb-bound bl-mod bl-bound
    isSigned factor offset minimum maximum unit presence receivers sig fb≤64 refl =
    record { def-wf = record
      { startBit-bound = sb-bound
      ; bitLength-bound = bl-bound
      } }
    , pv-LE refl
  postPresence-wf×pv frameBytes ctx name BigEndian sb-mod sb-bound bl-mod bl-bound
    isSigned factor offset minimum maximum unit presence receivers sig fb≤64 eq
    with 1 ≤ᵇ bl-mod in b1 | eq
  ... | false | ()
  ... | true | eq₁
    with (convertStartBit frameBytes BigEndian sb-mod bl-mod + bl-mod) ∸ 1 <ᵇ frameBytes * 8 in b2 | eq₁
  ... | false | ()
  ... | true | eq₂
    with bl-mod ∸ 1 ≤ᵇ convertStartBit frameBytes BigEndian sb-mod bl-mod in b3 | eq₂
  ... | false | ()
  ... | true | refl =
    record { def-wf = record
      { startBit-bound = convertSB-bound frameBytes BigEndian sb-mod bl-mod fb≤64 sb-bound
      ; bitLength-bound = bl-bound
      } }
    , pv-BE refl
        (≤ᵇ⇒≤ 1 bl-mod (subst T (sym b1) tt))
        (<ᵇ⇒< (convertStartBit frameBytes BigEndian sb-mod bl-mod + bl-mod ∸ 1) (frameBytes * 8) (subst T (sym b2) tt))
        (≤ᵇ⇒≤ (bl-mod ∸ 1) (convertStartBit frameBytes BigEndian sb-mod bl-mod) (subst T (sym b3) tt))

-- ============================================================================
-- COMBINED SIGNAL FIELDS WELL-FORMEDNESS + PHYSICAL VALIDITY
-- ============================================================================

-- If parseSignalFields succeeds, the result is both well-formed AND physically valid.
-- A single 11-deep with-chain (finding A15: eliminates the duplicate -wf/-pv chains).
-- Strategy: nested with on each lookup/parse step. Failure cases are absurd.
-- In the final success case, postPresence-wf×pv extracts both properties.
parseSignalFields-wf×pv : ∀ frameBytes ctx name obj sig
  → frameBytes ≤ 64
  → parseSignalFields frameBytes ctx name obj ≡ inj₂ sig
  → WellFormedSignal sig × PhysicallyValid frameBytes sig
parseSignalFields-wf×pv frameBytes ctx name obj sig fb≤64 eq
  with lookupNat "startBit" obj | eq
... | nothing | ()
... | just sb | eq₁
  with lookupNat "length" obj | eq₁
...   | nothing | ()
...   | just bl | eq₂
    with lookupChars "byteOrder" obj | eq₂
...     | nothing | ()
...     | just boStr | eq₃
      with parseByteOrder boStr | eq₃
...       | inj₁ _ | ()
...       | inj₂ bo | eq₄
        with parseSigned obj | eq₄
...         | inj₁ _ | ()
...         | inj₂ isSigned | eq₅
          with lookupDecRat "factor" obj | eq₅
...           | inj₁ _ | ()
...           | inj₂ factor | eq₆
            with lookupDecRat "offset" obj | eq₆
...             | inj₁ _ | ()
...             | inj₂ offset | eq₇
              with lookupDecRat "minimum" obj | eq₇
...               | inj₁ _ | ()
...               | inj₂ minimum | eq₈
                with lookupDecRat "maximum" obj | eq₈
...                 | inj₁ _ | ()
...                 | inj₂ maximum | eq₉
                  with lookupChars "unit" obj | eq₉
...                   | nothing | ()
...                   | just unit | eq₁₀
                    with parseSignalPresence obj | eq₁₀
...                     | inj₁ _ | ()
...                     | inj₂ presence | eq₁₁
                      with parseOptionalArray parseCharsList (lookupArray "receivers" obj) | eq₁₁
...                       | inj₁ _ | ()
...                       | inj₂ receivers | eq₁₂
                        with validateIdent name | eq₁₂
...                         | inj₁ _ | ()
...                         | inj₂ nameId | eq₁₃
                          with validateIdentList receivers | eq₁₃
...                           | inj₁ _ | ()
...                           | inj₂ receiverIds | eq₁₄ =
                                postPresence-wf×pv frameBytes ctx nameId bo
                                  (sb % max-physical-bits) (m%n<n sb max-physical-bits)
                                  (bl % suc max-physical-bits) (m%n<n bl (suc max-physical-bits))
                                  isSigned factor offset minimum maximum unit presence receiverIds sig fb≤64 eq₁₄

-- Projections of the combined proof (preserve backward-compatible API).
parseSignalFields-wf : ∀ frameBytes ctx name obj sig
  → frameBytes ≤ 64
  → parseSignalFields frameBytes ctx name obj ≡ inj₂ sig → WellFormedSignal sig
parseSignalFields-wf frameBytes ctx name obj sig fb≤64 eq =
  proj₁ (parseSignalFields-wf×pv frameBytes ctx name obj sig fb≤64 eq)

parseSignalFields-pv : ∀ frameBytes ctx name obj sig
  → frameBytes ≤ 64
  → parseSignalFields frameBytes ctx name obj ≡ inj₂ sig → PhysicallyValid frameBytes sig
parseSignalFields-pv frameBytes ctx name obj sig fb≤64 eq =
  proj₂ (parseSignalFields-wf×pv frameBytes ctx name obj sig fb≤64 eq)

-- ============================================================================
-- SIGNAL WELL-FORMEDNESS
-- ============================================================================

-- If parseSignal succeeds, the result is well-formed.
parseSignal-wf : ∀ frameBytes ctx obj sig
  → frameBytes ≤ 64
  → parseSignal frameBytes ctx obj ≡ inj₂ sig → WellFormedSignal sig
parseSignal-wf frameBytes ctx obj sig fb≤64 eq
  with lookupChars "name" obj | eq
... | nothing | ()
... | just name | eq' = parseSignalFields-wf frameBytes _ name obj sig fb≤64 eq'

-- ============================================================================
-- SIGNAL LIST: SHARED LIFT COMBINATOR
-- ============================================================================

-- Lift a per-element proof over parseSignalList's traversal.
-- P is indexed by frameBytes so it can be either constant (WellFormedSignal)
-- or dependent (PhysicallyValid frameBytes).
private
  parseSignalList-lift : ∀ {P : ℕ → DBCSignal → Set}
    → (∀ frameBytes ctx obj sig → frameBytes ≤ 64
       → parseSignal frameBytes ctx obj ≡ inj₂ sig → P frameBytes sig)
    → ∀ frameBytes ctx jsons idx sigs
    → frameBytes ≤ 64
    → parseSignalList frameBytes ctx jsons idx ≡ inj₂ sigs → All (P frameBytes) sigs
  parseSignalList-lift _ frameBytes ctx [] idx .[] fb≤64 refl = []
  parseSignalList-lift f frameBytes ctx (JObject sigObj ∷ rest) idx sigs fb≤64 eq
    with parseSignal frameBytes ctx sigObj in sig-eq | eq
  ... | inj₁ _ | ()
  ... | inj₂ sig | eq₁
    with parseSignalList frameBytes ctx rest (idx + 1) in rest-eq | eq₁
  ...   | inj₁ _ | ()
  ...   | inj₂ sigs' | refl = f frameBytes ctx sigObj sig fb≤64 sig-eq ∷
                               parseSignalList-lift f frameBytes ctx rest (idx + 1) sigs' fb≤64 rest-eq
  parseSignalList-lift _ frameBytes ctx (JNull     ∷ _) idx sigs fb≤64 ()
  parseSignalList-lift _ frameBytes ctx (JBool _   ∷ _) idx sigs fb≤64 ()
  parseSignalList-lift _ frameBytes ctx (JNumber _ ∷ _) idx sigs fb≤64 ()
  parseSignalList-lift _ frameBytes ctx (JString _ ∷ _) idx sigs fb≤64 ()
  parseSignalList-lift _ frameBytes ctx (JArray _  ∷ _) idx sigs fb≤64 ()

-- ============================================================================
-- SIGNAL LIST WELL-FORMEDNESS
-- ============================================================================

-- If parseSignalList succeeds, all signals are well-formed.
parseSignalList-wf : ∀ frameBytes ctx jsons idx sigs
  → frameBytes ≤ 64
  → parseSignalList frameBytes ctx jsons idx ≡ inj₂ sigs → All WellFormedSignal sigs
parseSignalList-wf = parseSignalList-lift parseSignal-wf

-- ============================================================================
-- SIGNAL PHYSICAL VALIDITY
-- ============================================================================

-- If parseSignal succeeds, the result is physically valid.
parseSignal-pv : ∀ frameBytes ctx obj sig
  → frameBytes ≤ 64
  → parseSignal frameBytes ctx obj ≡ inj₂ sig → PhysicallyValid frameBytes sig
parseSignal-pv frameBytes ctx obj sig fb≤64 eq
  with lookupChars "name" obj | eq
... | nothing | ()
... | just name | eq' = parseSignalFields-pv frameBytes _ name obj sig fb≤64 eq'

-- If parseSignalList succeeds, all signals are physically valid.
parseSignalList-pv : ∀ frameBytes ctx jsons idx sigs
  → frameBytes ≤ 64
  → parseSignalList frameBytes ctx jsons idx ≡ inj₂ sigs
  → All (PhysicallyValid frameBytes) sigs
parseSignalList-pv = parseSignalList-lift parseSignal-pv
