-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- The JSON parser reads back every string the formatter writes: each
-- character as the escape or the character the formatter wrote for it.
module Aletheia.Protocol.JSON.Properties.Roundtrip.String where

open import Data.Bool using (Bool; true; false; _∨_)
import Data.Bool
open import Data.Char using (_≈ᵇ_)
open import Data.Char.Base using (toℕ; fromℕ)
open import Data.Char.Properties using (toℕ-injective)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (map-id)
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _<ᵇ_; s≤s; z≤n)
open import Data.Nat.Properties using (<ᵇ⇒<; <⇒<ᵇ; ≮⇒≥)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)

open import Aletheia.Parser.Combinators using (mkResult; advancePosition; advancePositions; char; anyChar; satisfy; many; _*>_)
open import Aletheia.Parser.Properties.Success using (Reads; advancePositions-++; alt-right; before-just; bind-nothing; encodeAll; many-readback; reads-more; reads-none; reads-split; satisfy-just; satisfy-nothing; then-just)
open import Aletheia.Parser.Properties.Chars using (T⇒≡; ∨-cases; ∨-false; ≈ᵇ⇒≡)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Aletheia.Protocol.JSON.Format using (controlEscape; escapeChar; escapeOnto; showsString)
open import Aletheia.Protocol.JSON.Parse using (isUnescaped; decodeEscape; parseEscape; parseStringChar; parseStringChars)

-- ============================================================================
-- THE CONTROL CHARACTERS, ONE BY ONE
-- ============================================================================

-- Every character below U+0020 is written as an escape the parser reads back.
control-readback : ∀ n → n < 32 → ∀ pos rest →
  proj₂ (parseStringChar pos ('\\' ∷ controlEscape n rest))
    ≡ just (mkResult (fromℕ n) (advancePositions pos ('\\' ∷ controlEscape n [])) rest)
control-readback 0 _ pos rest = refl
control-readback 1 _ pos rest = refl
control-readback 2 _ pos rest = refl
control-readback 3 _ pos rest = refl
control-readback 4 _ pos rest = refl
control-readback 5 _ pos rest = refl
control-readback 6 _ pos rest = refl
control-readback 7 _ pos rest = refl
control-readback 8 _ pos rest = refl
control-readback 9 _ pos rest = refl
control-readback 10 _ pos rest = refl
control-readback 11 _ pos rest = refl
control-readback 12 _ pos rest = refl
control-readback 13 _ pos rest = refl
control-readback 14 _ pos rest = refl
control-readback 15 _ pos rest = refl
control-readback 16 _ pos rest = refl
control-readback 17 _ pos rest = refl
control-readback 18 _ pos rest = refl
control-readback 19 _ pos rest = refl
control-readback 20 _ pos rest = refl
control-readback (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))) _ pos rest = refl
control-readback (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))) _ pos rest = refl
control-readback (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))) _ pos rest = refl
control-readback (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))) _ pos rest = refl
control-readback (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))) _ pos rest = refl
control-readback (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))) _ pos rest = refl
control-readback (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))) _ pos rest = refl
control-readback (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))) _ pos rest = refl
control-readback (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))) _ pos rest = refl
control-readback (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))))) _ pos rest = refl
control-readback (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))))) _ pos rest = refl
control-readback (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))))))))))))))))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ())))))))))))))))))))))))))))))))) _ _

controlEscape-split : ∀ n → n < 32 → ∀ rest → controlEscape n rest ≡ controlEscape n [] ++ rest
controlEscape-split 0 _ rest = refl
controlEscape-split 1 _ rest = refl
controlEscape-split 2 _ rest = refl
controlEscape-split 3 _ rest = refl
controlEscape-split 4 _ rest = refl
controlEscape-split 5 _ rest = refl
controlEscape-split 6 _ rest = refl
controlEscape-split 7 _ rest = refl
controlEscape-split 8 _ rest = refl
controlEscape-split 9 _ rest = refl
controlEscape-split 10 _ rest = refl
controlEscape-split 11 _ rest = refl
controlEscape-split 12 _ rest = refl
controlEscape-split 13 _ rest = refl
controlEscape-split 14 _ rest = refl
controlEscape-split 15 _ rest = refl
controlEscape-split 16 _ rest = refl
controlEscape-split 17 _ rest = refl
controlEscape-split 18 _ rest = refl
controlEscape-split 19 _ rest = refl
controlEscape-split 20 _ rest = refl
controlEscape-split (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))) _ rest = refl
controlEscape-split (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))) _ rest = refl
controlEscape-split (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))) _ rest = refl
controlEscape-split (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))) _ rest = refl
controlEscape-split (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))) _ rest = refl
controlEscape-split (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))) _ rest = refl
controlEscape-split (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))) _ rest = refl
controlEscape-split (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))) _ rest = refl
controlEscape-split (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))) _ rest = refl
controlEscape-split (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))))) _ rest = refl
controlEscape-split (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))))) _ rest = refl
controlEscape-split (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))))))))))))))))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ())))))))))))))))))))))))))))))))) _

toℕ-fromℕ-small : ∀ n → n < 32 → toℕ (fromℕ n) ≡ n
toℕ-fromℕ-small 0 _ = refl
toℕ-fromℕ-small 1 _ = refl
toℕ-fromℕ-small 2 _ = refl
toℕ-fromℕ-small 3 _ = refl
toℕ-fromℕ-small 4 _ = refl
toℕ-fromℕ-small 5 _ = refl
toℕ-fromℕ-small 6 _ = refl
toℕ-fromℕ-small 7 _ = refl
toℕ-fromℕ-small 8 _ = refl
toℕ-fromℕ-small 9 _ = refl
toℕ-fromℕ-small 10 _ = refl
toℕ-fromℕ-small 11 _ = refl
toℕ-fromℕ-small 12 _ = refl
toℕ-fromℕ-small 13 _ = refl
toℕ-fromℕ-small 14 _ = refl
toℕ-fromℕ-small 15 _ = refl
toℕ-fromℕ-small 16 _ = refl
toℕ-fromℕ-small 17 _ = refl
toℕ-fromℕ-small 18 _ = refl
toℕ-fromℕ-small 19 _ = refl
toℕ-fromℕ-small 20 _ = refl
toℕ-fromℕ-small (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))) _ = refl
toℕ-fromℕ-small (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))) _ = refl
toℕ-fromℕ-small (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))) _ = refl
toℕ-fromℕ-small (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))) _ = refl
toℕ-fromℕ-small (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))) _ = refl
toℕ-fromℕ-small (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))) _ = refl
toℕ-fromℕ-small (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))) _ = refl
toℕ-fromℕ-small (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))) _ = refl
toℕ-fromℕ-small (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))) _ = refl
toℕ-fromℕ-small (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))))) _ = refl
toℕ-fromℕ-small (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))))))))))))))))))) _ = refl
toℕ-fromℕ-small (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))))))))))))))))))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))))))))))))))))))))))))))))

fromℕ-toℕ-small : ∀ c → toℕ c < 32 → fromℕ (toℕ c) ≡ c
fromℕ-toℕ-small c c< = toℕ-injective (fromℕ (toℕ c)) c (toℕ-fromℕ-small (toℕ c) c<)

-- ============================================================================
-- ONE CHARACTER
-- ============================================================================

private
  -- A character code not below 32 is above 31.
  above31 : ∀ n → (n <ᵇ 32) ≡ false → (31 <ᵇ n) ≡ true
  above31 n e = T⇒≡ (<⇒<ᵇ {31} {n} (≮⇒≥ {n} {32} (λ n<32 → contradiction (trans (sym e) (T⇒≡ (<⇒<ᵇ {n} {32} n<32))) (λ ()))))

  -- The formatter escapes the quotation mark and the reverse solidus with a `\`.
  escaped-readback : ∀ pos c rest → c ≡ '"' ⊎ c ≡ '\\' →
    proj₂ (parseStringChar pos ('\\' ∷ c ∷ rest)) ≡ just (mkResult c (advancePositions pos ('\\' ∷ c ∷ [])) rest)
  escaped-readback pos _ rest (inj₁ refl) = refl
  escaped-readback pos _ rest (inj₂ refl) = refl

  -- Every other character at or above U+0020 is written as itself.
  plain-readback : ∀ pos c rest → (toℕ c <ᵇ 32) ≡ false → (c ≈ᵇ '"') ≡ false → (c ≈ᵇ '\\') ≡ false →
    proj₂ (parseStringChar pos (c ∷ rest)) ≡ just (mkResult c (advancePosition pos c) rest)
  plain-readback pos c rest lt q s =
    trans (alt-right parseEscape (satisfy isUnescaped) pos (c ∷ rest)
            (bind-nothing (char '\\' *> anyChar) decodeEscape pos (c ∷ rest)
              (bind-nothing (char '\\') (λ _ → anyChar) pos (c ∷ rest) (satisfy-nothing (λ x → x ≈ᵇ '\\') pos c rest s))))
          (satisfy-just isUnescaped pos c rest unescaped)
    where
      unescaped : isUnescaped c ≡ true
      unescaped rewrite above31 (toℕ c) lt | q | s = refl

-- Every character the formatter writes, read back as itself.
escapeChar-readback : ∀ pos c rest →
  proj₂ (parseStringChar pos (escapeChar c rest)) ≡ just (mkResult c (advancePositions pos (escapeChar c [])) rest)
escapeChar-readback pos c rest with toℕ c <ᵇ 32 in lt
... | true =
  subst (λ v → proj₂ (parseStringChar pos ('\\' ∷ controlEscape (toℕ c) rest))
                 ≡ just (mkResult v (advancePositions pos ('\\' ∷ controlEscape (toℕ c) [])) rest))
        (fromℕ-toℕ-small c c<) (control-readback (toℕ c) c< pos rest)
  where
    c< : toℕ c < 32
    c< = <ᵇ⇒< (toℕ c) 32 (subst Data.Bool.T (sym lt) _)
... | false with (c ≈ᵇ '"') ∨ (c ≈ᵇ '\\') in q
...   | true  = escaped-readback pos c rest (Sum.map ≈ᵇ⇒≡ ≈ᵇ⇒≡ (∨-cases {c ≈ᵇ '"'} q))
...   | false = plain-readback pos c rest lt (proj₁ (∨-false {c ≈ᵇ '"'} q)) (proj₂ (∨-false {c ≈ᵇ '"'} q))

escapeChar-split : ∀ c rest → escapeChar c rest ≡ escapeChar c [] ++ rest
escapeChar-split c rest with toℕ c <ᵇ 32 in lt
... | true  = cong ('\\' ∷_) (controlEscape-split (toℕ c) (<ᵇ⇒< (toℕ c) 32 (subst Data.Bool.T (sym lt) _)) rest)
... | false with (c ≈ᵇ '"') ∨ (c ≈ᵇ '\\')
...   | true  = refl
...   | false = refl

escapeChar-nonempty : ∀ c → 0 < length (escapeChar c [])
escapeChar-nonempty c with toℕ c <ᵇ 32
... | true = s≤s z≤n
... | false with (c ≈ᵇ '"') ∨ (c ≈ᵇ '\\')
...   | true  = s≤s z≤n
...   | false = s≤s z≤n

-- ============================================================================
-- THE STRING
-- ============================================================================

escapeOnto-encodeAll : ∀ cs rest → escapeOnto cs rest ≡ encodeAll escapeChar cs rest
escapeOnto-encodeAll []       rest = refl
escapeOnto-encodeAll (c ∷ cs) rest = cong (escapeChar c) (escapeOnto-encodeAll cs rest)

-- The characters of a string, each read back, then its closing quotation mark.
string-reads : ∀ cs suffix → Reads parseStringChar escapeChar (λ c → c) ('"' ∷ suffix) cs
string-reads []       suffix = reads-none (λ pos → refl)
string-reads (c ∷ cs) suffix =
  reads-more (λ pos → escapeChar-readback pos c (encodeAll escapeChar cs ('"' ∷ suffix)))
             (escapeChar-split c) (escapeChar-nonempty c) (string-reads cs suffix)

-- Every string the formatter writes reads back as its characters.
showsString-readback : ∀ pos cs suffix →
  proj₂ (parseStringChars pos (showsString cs suffix)) ≡ just (mkResult cs (advancePositions pos (showsString cs [])) suffix)
showsString-readback pos cs suffix =
  subst₂ (λ body closed → proj₂ (parseStringChars pos ('"' ∷ body)) ≡ just (mkResult cs (advancePositions pos ('"' ∷ closed)) suffix))
    (sym (escapeOnto-encodeAll cs ('"' ∷ suffix))) (sym (escapeOnto-encodeAll cs ('"' ∷ [])))
    (trans (before-just (char '"' *> many parseStringChar) (char '"') pos ('"' ∷ encodeAll escapeChar cs ('"' ∷ suffix))
             (then-just (char '"') (many parseStringChar) pos ('"' ∷ encodeAll escapeChar cs ('"' ∷ suffix))
                        (satisfy-just (λ x → x ≈ᵇ '"') pos '"' (encodeAll escapeChar cs ('"' ∷ suffix)) refl)
                        (trans (many-readback (string-reads cs suffix) (advancePosition pos '"'))
                               (cong (λ v → just (mkResult v (advancePositions (advancePosition pos '"') (encodeAll escapeChar cs [])) ('"' ∷ suffix))) (map-id cs))))
             (satisfy-just (λ x → x ≈ᵇ '"') (advancePositions (advancePosition pos '"') (encodeAll escapeChar cs [])) '"' suffix refl))
           (cong (λ q → just (mkResult cs q suffix)) pos-eq))
  where
    pos-eq : advancePosition (advancePositions (advancePosition pos '"') (encodeAll escapeChar cs [])) '"'
             ≡ advancePositions (advancePosition pos '"') (encodeAll escapeChar cs ('"' ∷ []))
    pos-eq = sym (trans (cong (advancePositions (advancePosition pos '"')) (reads-split (string-reads cs suffix) ('"' ∷ [])))
                        (advancePositions-++ (advancePosition pos '"') (encodeAll escapeChar cs []) ('"' ∷ [])))
