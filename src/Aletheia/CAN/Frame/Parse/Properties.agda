-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- What the frame parser accepts is what its input says, and each refusal
-- names the condition that failed.
--
-- Acceptance: a field within its range is taken as it is (`*-accepts`), and
-- a payload of the DLC's length whose every byte is below 256 is taken byte
-- for byte; a parsed payload is exactly the list it was read from
-- (`parsePayload-exact`).  Refusal: each `ParseError` the parser builds
-- carries the offending value and holds only when its condition does
-- (`*-refuses`, `parsePayload-length-refusal`, `parsePayload-byte-refusal`).
module Aletheia.CAN.Frame.Parse.Properties where

open import Data.Bool using (Bool; true; false; T)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List as List using (List; []; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc; _+_; _<ᵇ_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Product using (Σ; _×_; _,_; ∃)
open import Data.Rational using (_/_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Vec as Vec using (Vec; []; _∷_; toList)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans)

open import Aletheia.CAN.Constants using (standard-can-id-max; extended-can-id-max)
open import Aletheia.CAN.DLC using (mkDLC; dlcBytes; maxDLC-FD)
open import Aletheia.CAN.Frame using (CANId; Standard; Extended; Byte; IsByte; AllBytes; []; _∷_)
open import Aletheia.CAN.Frame.Parse using
  ( Payload; check; consByte; parseCANId; parseDLC; parseParts; parsePayload; parseRational
  ; parseTimedFrame; parts; payload; walk )
open import Aletheia.Trace.Time using (mkTs)
open import Aletheia.Error using
  ( ParseError; StdCANIdOutOfRange; ExtCANIdOutOfRange; DLCCodeOutOfRange
  ; PayloadLengthMismatch; PayloadByteOutOfRange; NonPositiveDenominator )

-- ============================================================================
-- THE TEST COMBINATOR
-- ============================================================================

check-holds : ∀ {A B : Set} (b : Bool) (p : T b) (e : A) (k : T b → A ⊎ B) → check b e k ≡ k p
check-holds true tt e k = refl

-- A test whose continuation only accepts refuses with its own refusal, and
-- only when it fails.
check-refuses : ∀ {A B : Set} (b : Bool) (e : A) (f : T b → B) (r : A)
              → check b e (λ p → inj₂ (f p)) ≡ inj₁ r → r ≡ e × b ≡ false
check-refuses false e f .e refl = refl , refl

check-inj₂ : ∀ {A B : Set} (b : Bool) (e : A) (k : T b → A ⊎ B) (r : B)
           → check b e k ≡ inj₂ r → Σ (T b) λ p → k p ≡ inj₂ r
check-inj₂ true e k r eq = tt , eq

check-inj₁ : ∀ {A B : Set} (b : Bool) (e : A) (k : T b → A ⊎ B) (r : A)
           → check b e k ≡ inj₁ r → (r ≡ e × b ≡ false) ⊎ Σ (T b) λ p → k p ≡ inj₁ r
check-inj₁ false e k .e refl = inj₁ (refl , refl)
check-inj₁ true  e k r  eq   = inj₂ (tt , eq)

consByte-inj₂ : ∀ {n} b (pb : IsByte b) (w : ParseError ⊎ Payload n) (q : Payload (suc n))
              → consByte b pb w ≡ inj₂ q
              → ∃ λ (r : Payload n) → w ≡ inj₂ r × Payload.bytes q ≡ b ∷ Payload.bytes r
consByte-inj₂ b pb (inj₂ (payload v ok)) .(payload (b ∷ v) (pb ∷ ok)) refl = payload v ok , refl , refl

consByte-inj₁ : ∀ {n} b (pb : IsByte b) (w : ParseError ⊎ Payload n) e
              → consByte b pb w ≡ inj₁ e → w ≡ inj₁ e
consByte-inj₁ b pb (inj₁ e) .e refl = refl

-- ============================================================================
-- IDENTIFIER AND DLC
-- ============================================================================

parseCANId-standard-accepts : ∀ raw (p : T (raw <ᵇ standard-can-id-max))
                            → parseCANId raw false ≡ inj₂ (Standard raw p)
parseCANId-standard-accepts raw p = check-holds _ p (StdCANIdOutOfRange raw) (λ q → inj₂ (Standard raw q))

parseCANId-extended-accepts : ∀ raw (p : T (raw <ᵇ extended-can-id-max))
                            → parseCANId raw true ≡ inj₂ (Extended raw p)
parseCANId-extended-accepts raw p = check-holds _ p (ExtCANIdOutOfRange raw) (λ q → inj₂ (Extended raw q))

parseCANId-standard-refuses : ∀ raw e → parseCANId raw false ≡ inj₁ e
                            → e ≡ StdCANIdOutOfRange raw × (raw <ᵇ standard-can-id-max) ≡ false
parseCANId-standard-refuses raw e = check-refuses _ (StdCANIdOutOfRange raw) (λ q → Standard raw q) e

parseCANId-extended-refuses : ∀ raw e → parseCANId raw true ≡ inj₁ e
                            → e ≡ ExtCANIdOutOfRange raw × (raw <ᵇ extended-can-id-max) ≡ false
parseCANId-extended-refuses raw e = check-refuses _ (ExtCANIdOutOfRange raw) (λ q → Extended raw q) e

parseDLC-accepts : ∀ code (p : T (code <ᵇ suc maxDLC-FD)) → parseDLC code ≡ inj₂ (mkDLC code p)
parseDLC-accepts code p = check-holds _ p (DLCCodeOutOfRange code) (λ q → inj₂ (mkDLC code q))

parseDLC-refuses : ∀ code e → parseDLC code ≡ inj₁ e
                 → e ≡ DLCCodeOutOfRange code × (code <ᵇ suc maxDLC-FD) ≡ false
parseDLC-refuses code e = check-refuses _ (DLCCodeOutOfRange code) (λ q → mkDLC code q) e

-- ============================================================================
-- PAYLOAD
-- ============================================================================

walk-accepts : ∀ {n} i (v : Vec Byte n) (ok : AllBytes v) exp obs
             → walk n i (toList v) exp obs ≡ inj₂ (payload v ok)
walk-accepts i [] [] exp obs = refl
walk-accepts i (b ∷ v) (pb ∷ ok) exp obs =
  trans (check-holds _ pb (PayloadByteOutOfRange i b) (λ p → consByte b p (walk _ (suc i) (toList v) exp obs)))
        (cong (consByte b pb) (walk-accepts (suc i) v ok exp obs))

-- A payload of the DLC's length, every byte below 256, is taken byte for
-- byte.
parsePayload-accepts : ∀ dlc (v : Vec Byte (dlcBytes dlc)) (ok : AllBytes v)
                     → parsePayload dlc (toList v) ≡ inj₂ (payload v ok)
parsePayload-accepts dlc v ok = walk-accepts 0 v ok (dlcBytes dlc) (List.length (toList v))

walk-exact : ∀ n i bs exp obs (q : Payload n) → walk n i bs exp obs ≡ inj₂ q → toList (Payload.bytes q) ≡ bs
walk-exact zero    _ []       _   _   (payload [] _) refl = refl
walk-exact (suc n) i (b ∷ bs) exp obs q eq with check-inj₂ _ _ _ q eq
... | pb , eq′ with consByte-inj₂ b pb _ q eq′
...   | r , inner , bytes≡ = trans (cong toList bytes≡) (cong (b ∷_) (walk-exact n (suc i) bs exp obs r inner))

-- A parsed payload is exactly the list it was read from.
parsePayload-exact : ∀ dlc bs (q : Payload (dlcBytes dlc)) → parsePayload dlc bs ≡ inj₂ q
                   → toList (Payload.bytes q) ≡ bs
parsePayload-exact dlc bs = walk-exact (dlcBytes dlc) 0 bs (dlcBytes dlc) (List.length bs)

private
  suc-injective-≢ : ∀ {m n} → m ≢ n → suc m ≢ suc n
  suc-injective-≢ m≢n refl = m≢n refl

walk-length-refusal : ∀ n i bs exp obs e o → walk n i bs exp obs ≡ inj₁ (PayloadLengthMismatch e o)
                    → e ≡ exp × o ≡ obs × List.length bs ≢ n
walk-length-refusal zero    _ (_ ∷ _)  exp obs .exp .obs refl = refl , refl , λ ()
walk-length-refusal (suc n) _ []       exp obs .exp .obs refl = refl , refl , λ ()
walk-length-refusal (suc n) i (b ∷ bs) exp obs e o eq with check-inj₁ _ _ _ _ eq
... | inj₁ (() , _)
... | inj₂ (pb , eq′) with walk-length-refusal n (suc i) bs exp obs e o (consByte-inj₁ b pb _ _ eq′)
...   | e≡ , o≡ , len≢ = e≡ , o≡ , suc-injective-≢ len≢

-- A length mismatch reports the DLC's byte count and the list's length, and
-- only when they differ.
parsePayload-length-refusal : ∀ dlc bs e o → parsePayload dlc bs ≡ inj₁ (PayloadLengthMismatch e o)
                            → e ≡ dlcBytes dlc × o ≡ List.length bs × List.length bs ≢ dlcBytes dlc
parsePayload-length-refusal dlc bs = walk-length-refusal (dlcBytes dlc) 0 bs (dlcBytes dlc) (List.length bs)

walk-byte-refusal : ∀ n i bs exp obs j b → walk n i bs exp obs ≡ inj₁ (PayloadByteOutOfRange j b)
                  → ∃ λ d → j ≡ i + d × List.head (List.drop d bs) ≡ just b × (b <ᵇ 256) ≡ false
walk-byte-refusal zero    _ []      _ _ _ _ ()
walk-byte-refusal zero    _ (_ ∷ _) _ _ _ _ ()
walk-byte-refusal (suc n) _ []      _ _ _ _ ()
walk-byte-refusal (suc n) i (c ∷ bs) exp obs j b eq
  with check-inj₁ (c <ᵇ 256) (PayloadByteOutOfRange i c)
                  (λ p → consByte c p (walk n (suc i) bs exp obs)) (PayloadByteOutOfRange j b) eq
... | inj₁ (refl , out) = 0 , sym (+-identityʳ i) , refl , out
... | inj₂ (pc , eq′) with walk-byte-refusal n (suc i) bs exp obs j b (consByte-inj₁ c pc _ _ eq′)
...   | d , j≡ , at , out = suc d , trans j≡ (sym (+-suc i d)) , at , out

-- A byte refusal names a byte of the list at or above 256, at the position
-- it gives.
parsePayload-byte-refusal : ∀ dlc bs j b → parsePayload dlc bs ≡ inj₁ (PayloadByteOutOfRange j b)
                          → List.head (List.drop j bs) ≡ just b × (b <ᵇ 256) ≡ false
parsePayload-byte-refusal dlc bs j b eq with walk-byte-refusal (dlcBytes dlc) 0 bs (dlcBytes dlc) (List.length bs) j b eq
... | d , refl , at , out = at , out

-- ============================================================================
-- FRAME
-- ============================================================================

-- A frame whose identifier and DLC parse is taken with the payload as given.
parseParts-accepts
  : ∀ raw ext code {canId dlc}
  → parseCANId raw ext ≡ inj₂ canId → parseDLC code ≡ inj₂ dlc
  → (v : Vec Byte (dlcBytes dlc)) (ok : AllBytes v)
  → parseParts raw ext code (toList v) ≡ inj₂ (parts canId dlc (payload v ok))
parseParts-accepts raw ext code {canId} {dlc} idOk dlcOk v ok with parseCANId raw ext | idOk
... | .(inj₂ canId) | refl with parseDLC code | dlcOk
...   | .(inj₂ dlc) | refl with parsePayload dlc (toList v) | parsePayload-accepts dlc v ok
...     | .(inj₂ (payload v ok)) | refl = refl

parseTimedFrame-accepts
  : ∀ ts raw ext code brs esi {canId dlc}
  → parseCANId raw ext ≡ inj₂ canId → parseDLC code ≡ inj₂ dlc
  → (v : Vec Byte (dlcBytes dlc)) (ok : AllBytes v)
  → parseTimedFrame ts raw ext code (toList v) brs esi
    ≡ inj₂ (record
      { timestamp = mkTs ts
      ; payloadSize = dlcBytes dlc
      ; frame = record { id = canId ; dlc = dlc ; payload = v ; below256 = ok }
      ; dlcValid = refl
      ; brs = brs
      ; esi = esi })
parseTimedFrame-accepts ts raw ext code brs esi {canId} {dlc} idOk dlcOk v ok
  with parseParts raw ext code (toList v) | parseParts-accepts raw ext code idOk dlcOk v ok
... | .(inj₂ (parts canId dlc (payload v ok))) | refl = refl

-- ============================================================================
-- SIGNAL VALUES
-- ============================================================================

parseRational-accepts : ∀ n d → parseRational n (+ suc d) ≡ inj₂ (n / suc d)
parseRational-accepts n d = refl

parseRational-refuses-zero : ∀ n → parseRational n (+ 0) ≡ inj₁ (NonPositiveDenominator (+ 0))
parseRational-refuses-zero n = refl

parseRational-refuses-negative : ∀ n k → parseRational n -[1+ k ] ≡ inj₁ (NonPositiveDenominator -[1+ k ])
parseRational-refuses-negative n k = refl
