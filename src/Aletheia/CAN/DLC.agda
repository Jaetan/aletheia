{-# OPTIONS --safe --without-K #-}

-- CAN-FD Data Length Code (DLC) to payload byte count mapping.
--
-- Purpose: Convert between DLC field values and actual payload sizes.
-- CAN 2.0B: DLC 0–8 maps directly to 0–8 bytes.
-- CAN-FD:   DLC 9–15 maps to 12, 16, 20, 24, 32, 48, 64 bytes.
-- Role: Used by frame construction, validation, and protocol layers.
module Aletheia.CAN.DLC where

open import Data.Nat using (ℕ; suc; _+_; _≤_; z≤n; _≡ᵇ_)
open import Data.Nat.Properties using (m≤m+n; ≤-refl; ≤-trans; 1+n≰n)
open import Data.Bool using (if_then_else_)
open import Data.Maybe using (Maybe; just; nothing; Is-just)
open import Data.Maybe.Relation.Unary.Any using () renaming (just to is-just)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

-- CAN-FD DLC to payload byte count.
-- DLC 0–8: identity mapping (CAN 2.0B compatible).
-- DLC 9–15: non-linear mapping per ISO 11898-1:2015.
-- DLC > 15: returns the value unchanged (invalid, caught by validation).
dlcToBytes : ℕ → ℕ
dlcToBytes 9  = 12
dlcToBytes 10 = 16
dlcToBytes 11 = 20
dlcToBytes 12 = 24
dlcToBytes 13 = 32
dlcToBytes 14 = 48
dlcToBytes 15 = 64
dlcToBytes n  = n

-- Inverse: payload byte count to DLC.
-- Returns nothing for byte counts that don't correspond to valid DLC values.
-- Uses ≡ᵇ for large literals (≥20) to avoid LiteralTooBig / suc pile-ups.
bytesToDlc : ℕ → Maybe ℕ
bytesToDlc 0  = just 0
bytesToDlc 1  = just 1
bytesToDlc 2  = just 2
bytesToDlc 3  = just 3
bytesToDlc 4  = just 4
bytesToDlc 5  = just 5
bytesToDlc 6  = just 6
bytesToDlc 7  = just 7
bytesToDlc 8  = just 8
bytesToDlc 12 = just 9
bytesToDlc 16 = just 10
bytesToDlc n  =
  if n ≡ᵇ 20 then just 11
  else if n ≡ᵇ 24 then just 12
  else if n ≡ᵇ 32 then just 13
  else if n ≡ᵇ 48 then just 14
  else if n ≡ᵇ 64 then just 15
  else nothing

-- Maximum DLC value for CAN 2.0B
maxDLC-2B : ℕ
maxDLC-2B = 8

-- Maximum DLC value for CAN-FD
maxDLC-FD : ℕ
maxDLC-FD = 15

-- ============================================================================
-- DLC ROUNDTRIP AND BOUND PROPERTIES
-- ============================================================================

-- Helper: values ≥ 16 can't be ≤ 15
private
  16+k≰15 : ∀ {k} → 16 + k ≤ 15 → ⊥
  16+k≰15 {k} p = 1+n≰n (≤-trans p (m≤m+n 15 k))

-- Roundtrip: bytesToDlc recovers the original DLC code from dlcToBytes.
-- Each of the 16 valid DLC codes (0–15) reduces to refl by computation.
bytesToDlc-dlcToBytes : ∀ d → d ≤ 15 → bytesToDlc (dlcToBytes d) ≡ just d
bytesToDlc-dlcToBytes  0 _ = refl
bytesToDlc-dlcToBytes  1 _ = refl
bytesToDlc-dlcToBytes  2 _ = refl
bytesToDlc-dlcToBytes  3 _ = refl
bytesToDlc-dlcToBytes  4 _ = refl
bytesToDlc-dlcToBytes  5 _ = refl
bytesToDlc-dlcToBytes  6 _ = refl
bytesToDlc-dlcToBytes  7 _ = refl
bytesToDlc-dlcToBytes  8 _ = refl
bytesToDlc-dlcToBytes  9 _ = refl
bytesToDlc-dlcToBytes 10 _ = refl
bytesToDlc-dlcToBytes 11 _ = refl
bytesToDlc-dlcToBytes 12 _ = refl
bytesToDlc-dlcToBytes 13 _ = refl
bytesToDlc-dlcToBytes 14 _ = refl
bytesToDlc-dlcToBytes 15 _ = refl
bytesToDlc-dlcToBytes (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))))))))) d≤15 =
  ⊥-elim (16+k≰15 d≤15)

-- Upper bound: valid DLC codes produce payloads of at most 64 bytes.
dlcToBytes-bounded : ∀ d → d ≤ 15 → dlcToBytes d ≤ 64
dlcToBytes-bounded  0 _ = z≤n
dlcToBytes-bounded  1 _ = m≤m+n 1 63
dlcToBytes-bounded  2 _ = m≤m+n 2 62
dlcToBytes-bounded  3 _ = m≤m+n 3 61
dlcToBytes-bounded  4 _ = m≤m+n 4 60
dlcToBytes-bounded  5 _ = m≤m+n 5 59
dlcToBytes-bounded  6 _ = m≤m+n 6 58
dlcToBytes-bounded  7 _ = m≤m+n 7 57
dlcToBytes-bounded  8 _ = m≤m+n 8 56
dlcToBytes-bounded  9 _ = m≤m+n 12 52
dlcToBytes-bounded 10 _ = m≤m+n 16 48
dlcToBytes-bounded 11 _ = m≤m+n 20 44
dlcToBytes-bounded 12 _ = m≤m+n 24 40
dlcToBytes-bounded 13 _ = m≤m+n 32 32
dlcToBytes-bounded 14 _ = m≤m+n 48 16
dlcToBytes-bounded 15 _ = ≤-refl
dlcToBytes-bounded (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))))))))) d≤15 =
  ⊥-elim (16+k≰15 d≤15)

-- Injectivity: distinct valid DLC codes map to distinct byte counts.
-- Follows algebraically from the forward roundtrip — no case analysis needed.
dlcToBytes-injective : ∀ d₁ d₂ → d₁ ≤ 15 → d₂ ≤ 15
                     → dlcToBytes d₁ ≡ dlcToBytes d₂ → d₁ ≡ d₂
dlcToBytes-injective d₁ d₂ d₁≤15 d₂≤15 eq =
  just-inj (trans (sym (bytesToDlc-dlcToBytes d₁ d₁≤15))
                  (trans (cong bytesToDlc eq)
                         (bytesToDlc-dlcToBytes d₂ d₂≤15)))
  where
    just-inj : ∀ {A : Set} {a b : A} → just a ≡ just b → a ≡ b
    just-inj refl = refl

-- Completeness: every valid DLC code is the image of exactly one byte count
-- under bytesToDlc, and dlcToBytes recovers that byte count.
-- Matches on d (0–15) instead of b (0–64) to avoid LiteralTooBig on patterns > 20.
-- Combined with bytesToDlc-dlcToBytes, gives full bidirectional characterization.
bytesToDlc-complete : ∀ d → d ≤ 15
  → Σ[ b ∈ ℕ ] (bytesToDlc b ≡ just d × dlcToBytes d ≡ b)
bytesToDlc-complete  0 _ = 0  , refl , refl
bytesToDlc-complete  1 _ = 1  , refl , refl
bytesToDlc-complete  2 _ = 2  , refl , refl
bytesToDlc-complete  3 _ = 3  , refl , refl
bytesToDlc-complete  4 _ = 4  , refl , refl
bytesToDlc-complete  5 _ = 5  , refl , refl
bytesToDlc-complete  6 _ = 6  , refl , refl
bytesToDlc-complete  7 _ = 7  , refl , refl
bytesToDlc-complete  8 _ = 8  , refl , refl
bytesToDlc-complete  9 _ = 12 , refl , refl
bytesToDlc-complete 10 _ = 16 , refl , refl
bytesToDlc-complete 11 _ = 20 , refl , refl
bytesToDlc-complete 12 _ = 24 , refl , refl
bytesToDlc-complete 13 _ = 32 , refl , refl
bytesToDlc-complete 14 _ = 48 , refl , refl
bytesToDlc-complete 15 _ = 64 , refl , refl
bytesToDlc-complete (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))))))))) d≤15 =
  ⊥-elim (16+k≰15 d≤15)

-- Connection to ValidDLC: valid DLC codes produce recognized byte counts.
-- Useful for constructing ValidDBC proofs from DLC code bounds.
dlcToBytes-Is-just : ∀ d → d ≤ 15 → Is-just (bytesToDlc (dlcToBytes d))
dlcToBytes-Is-just d d≤15 rewrite bytesToDlc-dlcToBytes d d≤15 = is-just tt
