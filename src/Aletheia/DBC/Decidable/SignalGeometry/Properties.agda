-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Acceptance and inversion lemmas for the shared geometry gate core
-- (`SignalGeometry.geometryRefusal`).  Acceptance turns the per-byte-order
-- condition set into `geometryRefusal ≡ nothing` (consumed by the
-- emit→re-parse roundtrip proofs, which rewrite the gate away); inversion
-- recovers the conditions from a passed gate (consumed by the parser WF
-- proofs — the gate witnesses ARE the well-formedness certificates).
module Aletheia.DBC.Decidable.SignalGeometry.Properties where

open import Data.Bool using (T; true; false)
open import Data.Maybe using (nothing)
open import Data.Nat using (_*_; _∸_; _<_; _≤_; _≤ᵇ_; _<ᵇ_)
open import Data.Nat.Properties using (≤ᵇ⇒≤; <ᵇ⇒<)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary.Decidable using (dec-true)

open import Aletheia.CAN.Endianness using (BigEndian; physicalBitPos)
open import Aletheia.DBC.Decidable.SignalGeometry using
  ( startBitInFrame?; bitLengthInFrame?; bitLengthPositive?; bigEndianNoWrap?
  ; geometryRefusal )
open import Aletheia.CAN.Endianness using (LittleEndian)

-- ── acceptance ───────────────────────────────────────────────────────────────

geometryRefusal-accept-LE : ∀ fb sb bl
  → 1 ≤ bl → sb < fb * 8 → bl ≤ fb * 8
  → geometryRefusal fb LittleEndian sb bl ≡ nothing
geometryRefusal-accept-LE fb sb bl lp sbF blF
  rewrite dec-true (bitLengthPositive? bl) lp
        | dec-true (startBitInFrame? fb sb) sbF
        | dec-true (bitLengthInFrame? fb bl) blF
  = refl

geometryRefusal-accept-BE : ∀ fb sb bl
  → 1 ≤ bl → sb < fb * 8 → bl ≤ fb * 8
  → bl ∸ 1 ≤ physicalBitPos fb BigEndian sb
  → geometryRefusal fb BigEndian sb bl ≡ nothing
geometryRefusal-accept-BE fb sb bl lp sbF blF nw
  rewrite dec-true (bitLengthPositive? bl) lp
        | dec-true (startBitInFrame? fb sb) sbF
        | dec-true (bitLengthInFrame? fb bl) blF
        | dec-true (bigEndianNoWrap? fb sb bl) nw
  = refl

-- ── inversion ────────────────────────────────────────────────────────────────

-- The deciders' `does` fields normalize to the raw Bool comparisons, so the
-- inversion chains abstract those scrutinees with `in`-equations (the house
-- `with … in b | eq` pattern) and recover the ordering proofs via
-- `≤ᵇ⇒≤` / `<ᵇ⇒<`.

geometryRefusal-inv-LE : ∀ fb sb bl
  → geometryRefusal fb LittleEndian sb bl ≡ nothing
  → (1 ≤ bl) × (sb < fb * 8) × (bl ≤ fb * 8)
geometryRefusal-inv-LE fb sb bl eq with 1 ≤ᵇ bl in b1 | eq
... | false | ()
... | true  | eq₁ with sb <ᵇ fb * 8 in b2 | eq₁
...   | false | ()
...   | true  | eq₂ with bl ≤ᵇ fb * 8 in b3 | eq₂
...     | false | ()
...     | true  | _ =
          ≤ᵇ⇒≤ 1 bl (subst T (sym b1) tt) ,
          <ᵇ⇒< sb (fb * 8) (subst T (sym b2) tt) ,
          ≤ᵇ⇒≤ bl (fb * 8) (subst T (sym b3) tt)

geometryRefusal-inv-BE : ∀ fb sb bl
  → geometryRefusal fb BigEndian sb bl ≡ nothing
  → (1 ≤ bl) × (sb < fb * 8) × (bl ≤ fb * 8)
      × (bl ∸ 1 ≤ physicalBitPos fb BigEndian sb)
geometryRefusal-inv-BE fb sb bl eq with 1 ≤ᵇ bl in b1 | eq
... | false | ()
... | true  | eq₁ with sb <ᵇ fb * 8 in b2 | eq₁
...   | false | ()
...   | true  | eq₂ with bl ≤ᵇ fb * 8 in b3 | eq₂
...     | false | ()
...     | true  | eq₃ with bl ∸ 1 ≤ᵇ physicalBitPos fb BigEndian sb in b4 | eq₃
...       | false | ()
...       | true  | _ =
            ≤ᵇ⇒≤ 1 bl (subst T (sym b1) tt) ,
            <ᵇ⇒< sb (fb * 8) (subst T (sym b2) tt) ,
            ≤ᵇ⇒≤ bl (fb * 8) (subst T (sym b3) tt) ,
            ≤ᵇ⇒≤ (bl ∸ 1) (physicalBitPos fb BigEndian sb) (subst T (sym b4) tt)
