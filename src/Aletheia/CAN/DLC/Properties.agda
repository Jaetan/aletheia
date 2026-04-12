{-# OPTIONS --safe --without-K #-}

-- DLC roundtrip, bound, and injectivity properties.
--
-- Purpose: Prove correctness properties of the DLC ↔ byte count mapping.
-- Properties:
--   bytesToDlc-dlcToBytes : roundtrip (bytesToDlc ∘ dlcToBytes ≡ just)
--   dlcToBytes-bounded    : valid DLC codes produce payloads ≤ 64 bytes
--   dlcToBytes-injective  : distinct valid DLC codes → distinct byte counts
--   bytesToDlc-complete   : every valid DLC code is in the image of bytesToDlc
--   dlcToBytes-Is-just    : Is-just predicate bridge
module Aletheia.CAN.DLC.Properties where

open import Aletheia.CAN.DLC using (DLC; mkDLC; dlcToBytes; dlcBytes; bytesToDlc; bytesToValidDLC)
open import Data.Nat using (ℕ; suc; _+_; _≤_; _≡ᵇ_; z≤n)
open import Data.Nat.Properties using (m≤m+n; ≤-refl; ≤-trans; 1+n≰n; ≡ᵇ⇒≡)
open import Data.Maybe using (just; Is-just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Maybe.Relation.Unary.Any using () renaming (just to is-just)
open import Data.Bool using (Bool; true; false; T)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

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
  just-injective (trans (sym (bytesToDlc-dlcToBytes d₁ d₁≤15))
                        (trans (cong bytesToDlc eq)
                               (bytesToDlc-dlcToBytes d₂ d₂≤15)))

-- Completeness: every valid DLC code is the image of exactly one byte count
-- under bytesToDlc, and dlcToBytes recovers that byte count.
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

-- Valid DLC codes produce recognized byte counts (Is-just predicate).
-- Useful for constructing ValidDBC proofs from DLC code bounds.
dlcToBytes-Is-just : ∀ d → d ≤ 15 → Is-just (bytesToDlc (dlcToBytes d))
dlcToBytes-Is-just d d≤15 rewrite bytesToDlc-dlcToBytes d d≤15 = is-just tt

-- Inverse direction: when bytesToValidDLC succeeds with `just d`, the DLC's
-- byte count agrees with the input byte count. Each literal case reduces to
-- refl after pattern-matching the resulting `d`. The catch-all (n ≥ 17) walks
-- the if/≡ᵇ chain mirroring bytesToValidDLC's definition.
bvd-bytes : ∀ n d → bytesToValidDLC n ≡ just d → dlcBytes d ≡ n
bvd-bytes 0  .(mkDLC 0  tt) refl = refl
bvd-bytes 1  .(mkDLC 1  tt) refl = refl
bvd-bytes 2  .(mkDLC 2  tt) refl = refl
bvd-bytes 3  .(mkDLC 3  tt) refl = refl
bvd-bytes 4  .(mkDLC 4  tt) refl = refl
bvd-bytes 5  .(mkDLC 5  tt) refl = refl
bvd-bytes 6  .(mkDLC 6  tt) refl = refl
bvd-bytes 7  .(mkDLC 7  tt) refl = refl
bvd-bytes 8  .(mkDLC 8  tt) refl = refl
bvd-bytes 9  _ ()
bvd-bytes 10 _ ()
bvd-bytes 11 _ ()
bvd-bytes 12 .(mkDLC 9  tt) refl = refl
bvd-bytes 13 _ ()
bvd-bytes 14 _ ()
bvd-bytes 15 _ ()
bvd-bytes 16 .(mkDLC 10 tt) refl = refl
bvd-bytes n@(suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _))))))))))))))))) d eq
  with n ≡ᵇ 20 in eq₂₀ | eq
... | true  | refl = sym (≡ᵇ⇒≡ n 20 (subst T (sym eq₂₀) tt))
... | false | eq₁ with n ≡ᵇ 24 in eq₂₄ | eq₁
...   | true  | refl = sym (≡ᵇ⇒≡ n 24 (subst T (sym eq₂₄) tt))
...   | false | eq₂ with n ≡ᵇ 32 in eq₃₂ | eq₂
...     | true  | refl = sym (≡ᵇ⇒≡ n 32 (subst T (sym eq₃₂) tt))
...     | false | eq₃ with n ≡ᵇ 48 in eq₄₈ | eq₃
...       | true  | refl = sym (≡ᵇ⇒≡ n 48 (subst T (sym eq₄₈) tt))
...       | false | eq₄ with n ≡ᵇ 64 in eq₆₄ | eq₄
...         | true  | refl = sym (≡ᵇ⇒≡ n 64 (subst T (sym eq₆₄) tt))
...         | false | ()

-- Roundtrip: bytesToValidDLC recovers the original DLC record from dlcBytes.
-- Each of the 16 valid DLC codes (0–15) reduces to refl by computation.
bytesToValidDLC-roundtrip : ∀ (d : DLC) → bytesToValidDLC (dlcBytes d) ≡ just d
bytesToValidDLC-roundtrip (mkDLC 0 _) = refl
bytesToValidDLC-roundtrip (mkDLC 1 _) = refl
bytesToValidDLC-roundtrip (mkDLC 2 _) = refl
bytesToValidDLC-roundtrip (mkDLC 3 _) = refl
bytesToValidDLC-roundtrip (mkDLC 4 _) = refl
bytesToValidDLC-roundtrip (mkDLC 5 _) = refl
bytesToValidDLC-roundtrip (mkDLC 6 _) = refl
bytesToValidDLC-roundtrip (mkDLC 7 _) = refl
bytesToValidDLC-roundtrip (mkDLC 8 _) = refl
bytesToValidDLC-roundtrip (mkDLC 9 _) = refl
bytesToValidDLC-roundtrip (mkDLC 10 _) = refl
bytesToValidDLC-roundtrip (mkDLC 11 _) = refl
bytesToValidDLC-roundtrip (mkDLC 12 _) = refl
bytesToValidDLC-roundtrip (mkDLC 13 _) = refl
bytesToValidDLC-roundtrip (mkDLC 14 _) = refl
bytesToValidDLC-roundtrip (mkDLC 15 _) = refl
bytesToValidDLC-roundtrip (mkDLC (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))))))))) ())
