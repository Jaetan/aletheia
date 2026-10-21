-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- The JSON parser reads back every integer the formatter writes whose
-- magnitude is below 2^64, as the rational the integer is.
module Aletheia.Protocol.JSON.Properties.Roundtrip.Number where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char; _≈ᵇ_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer using (ℤ; +_; -[1+_]; ∣_∣)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to All-++⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _/_; _%_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.DivMod using (m/n<m; m%n<n; m≡m%n+[m/n]*n)
open import Data.Nat.Induction using (<-wellFounded-fast)
open import Data.Nat.Properties using (≤-trans; ≤-pred; ≤-refl; n≤1+n; <-irrefl; ≤-<-trans; *-identityʳ; +-identityʳ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₂)
open import Data.Rational using (ℚ; mkℚ)
open import Data.Nat.Coprimality using (Coprime)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)

open import Aletheia.Parser.Combinators using (Parser; mkResult; advancePosition; advancePositions; satisfy; char; many; optional; _<$>_; _<*>_; _<|>_; _*>_)
open import Aletheia.Parser.Properties.Success using (alt-left; alt-right; ap-just; ap-nothing; bind-nothing; map-just; map-nothing; optional-just; optional-nothing; satisfy-just; satisfy-nothing)
open import Aletheia.Parser.Properties.Chars using (∧-left; ∧-right; not-true; ≈ᵇ⇒≡)
open import Data.Bool.Properties using (¬-not)
open import Relation.Nullary.Negation using (contradiction)
open import Aletheia.DBC.DecRat using (toℚ; fromℤ; canonicalizeDecRat)
open import Aletheia.DBC.DecRat.Literal using (scientificLiteral; decimalLiteral; signedDecRat; rawLiteral; rawFromSignificand; applySign; significand; foldDigits; heldMagnitude)
open import Aletheia.DBC.DecRat.Literal.Properties using (literal-verdict; exact; held; exactTriple; canonical; LargeComponent)
open import Aletheia.DBC.TextFormatter.Emitter using (digitChar; showNat-chars; showNat-chars-fuel)
open import Aletheia.DBC.TextParser.DecRatParse.Properties.Phase1Digits using (foldDigits-showNat-chars)
open import Aletheia.DBC.TextParser.DecRatParse.Properties.Phase2Many using (SuffixStops; []-stop; ∷-stop; manyHelper-satisfy-exhaust-many)
open import Aletheia.DBC.TextParser.DecRatParse.Properties.Phase3Naturals using (signedDecRat-canon-+; signedDecRat-canon-neg)
open import Aletheia.DBC.TextParser.DecRatParse.Properties.Phase6Suffix using (canonicalizeDecRat-zero-exp)
open import Aletheia.Protocol.JSON.Format using (digitsOnto; showsℕ; showsℤ)
open import Aletheia.Protocol.JSON.Parse using (isDigitChar; isNonZeroDigit; digit; digitRun; parseIntPart; exponentParts; parseExponent; literalValue; parseRational; parseNumber)
open import Aletheia.Protocol.JSON.Types using (JSON; JNumber)

-- ============================================================================
-- THE DIGIT WRITER IS `showNat-chars`
-- ============================================================================

private
  fuel-zero : ∀ f n → n / 10 ≡ 0 → showNat-chars-fuel (suc f) n ≡ digitChar (n % 10) ∷ []
  fuel-zero f n e with n / 10 | e
  ... | zero | refl = refl

  fuel-suc : ∀ f n m → n / 10 ≡ suc m →
    showNat-chars-fuel (suc f) n ≡ showNat-chars-fuel f (suc m) ++ digitChar (n % 10) ∷ []
  fuel-suc f n m e with n / 10 | e
  ... | suc .m | refl = refl

digitsOnto-fuel : ∀ f k (a : Acc _<_ (suc k)) rest → suc k ≤ f →
  digitsOnto (suc k) a rest ≡ showNat-chars-fuel f (suc k) ++ rest
digitsOnto-fuel (suc f) k (acc rec) rest (s≤s k≤f) =
  go (suc k / 10) (rec (m/n<m (suc k) 10 (s≤s (s≤s z≤n)))) refl (m/n<m (suc k) 10 (s≤s (s≤s z≤n)))
  where
    d = digitChar (suc k % 10)
    go : ∀ q (a : Acc _<_ q) → suc k / 10 ≡ q → q < suc k →
      digitsOnto q a (d ∷ rest) ≡ showNat-chars-fuel (suc f) (suc k) ++ rest
    go zero    _ e _ = cong (_++ rest) (sym (fuel-zero f (suc k) e))
    go (suc m) a e q< =
      trans (digitsOnto-fuel f m a (d ∷ rest) (≤-trans (≤-pred q<) k≤f))
            (trans (sym (++-assoc (showNat-chars-fuel f (suc m)) (d ∷ []) rest))
                   (cong (_++ rest) (sym (fuel-suc f (suc k) m e))))

showsℕ-chars : ∀ n rest → showsℕ n rest ≡ showNat-chars n ++ rest
showsℕ-chars zero    rest = refl
showsℕ-chars (suc k) rest = digitsOnto-fuel (suc (suc k)) k (<-wellFounded-fast (suc k)) rest (n≤1+n (suc k))

-- The characters of an integer.
intChars : ℤ → List Char
intChars z = showsℤ z []

showsℤ-chars : ∀ z rest → showsℤ z rest ≡ intChars z ++ rest
showsℤ-chars (+ n) rest =
  trans (showsℕ-chars n rest) (cong (_++ rest) (sym (trans (showsℕ-chars n []) (++-identityʳ _))))
showsℤ-chars -[1+ n ] rest =
  cong ('-' ∷_) (trans (showsℕ-chars (suc n) rest) (cong (_++ rest) (sym (trans (showsℕ-chars (suc n) []) (++-identityʳ _)))))

-- ============================================================================
-- THE DIGITS
-- ============================================================================

digitChar-digit : ∀ d → d < 10 → isDigitChar (digitChar d) ≡ true
digitChar-digit 0 _ = refl
digitChar-digit 1 _ = refl
digitChar-digit 2 _ = refl
digitChar-digit 3 _ = refl
digitChar-digit 4 _ = refl
digitChar-digit 5 _ = refl
digitChar-digit 6 _ = refl
digitChar-digit 7 _ = refl
digitChar-digit 8 _ = refl
digitChar-digit 9 _ = refl
digitChar-digit (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))))))

digitChar-nonzero : ∀ d → 0 < d → d < 10 → isNonZeroDigit (digitChar d) ≡ true
digitChar-nonzero 1 _ _ = refl
digitChar-nonzero 2 _ _ = refl
digitChar-nonzero 3 _ _ = refl
digitChar-nonzero 4 _ _ = refl
digitChar-nonzero 5 _ _ = refl
digitChar-nonzero 6 _ _ = refl
digitChar-nonzero 7 _ _ = refl
digitChar-nonzero 8 _ _ = refl
digitChar-nonzero 9 _ _ = refl
digitChar-nonzero (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) _
  (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ()))))))))))

All-digit-fuel : ∀ f n → All (λ c → isDigitChar c ≡ true) (showNat-chars-fuel f n)
All-digit-fuel zero    _ = []
All-digit-fuel (suc f) n with n / 10
... | zero  = digitChar-digit (n % 10) (m%n<n n 10) ∷ []
... | suc m = All-++⁺ (All-digit-fuel f (suc m)) (digitChar-digit (n % 10) (m%n<n n 10) ∷ [])

private
  n%10≡n : ∀ n → n / 10 ≡ 0 → n % 10 ≡ n
  n%10≡n n e = sym (trans (m≡m%n+[m/n]*n n 10) (trans (cong (λ q → n % 10 + q * 10) e) (+-identityʳ (n % 10))))

  quot≤ : ∀ n m f → 0 < n → n ≤ suc f → n / 10 ≡ suc m → suc m ≤ f
  quot≤ (suc k) m f _ n≤ e = ≤-pred (≤-trans (subst (_< suc k) e (m/n<m (suc k) 10 (s≤s (s≤s z≤n)))) n≤)

-- A positive number's digits start with a digit other than `0`.
lead-fuel : ∀ f n → 0 < n → n ≤ f →
  Σ[ c ∈ Char ] Σ[ cs ∈ List Char ] (showNat-chars-fuel (suc f) n ≡ c ∷ cs × isNonZeroDigit c ≡ true)
lead-fuel zero    zero    () _
lead-fuel zero    (suc _) _  ()
lead-fuel (suc f) n 0<n n≤f with n / 10 in e
... | zero  = digitChar (n % 10) , [] , refl ,
              digitChar-nonzero (n % 10) (subst (0 <_) (sym (n%10≡n n e)) 0<n) (m%n<n n 10)
... | suc m with lead-fuel f (suc m) (s≤s z≤n) (quot≤ n m f 0<n n≤f e)
...   | c , cs , eq , nz = c , cs ++ digitChar (n % 10) ∷ [] , cong (_++ digitChar (n % 10) ∷ []) eq , nz

-- ============================================================================
-- THE INTEGER PART
-- ============================================================================

-- A digit is no character the digit test refuses.
digit-≉ : ∀ {c} d → isDigitChar c ≡ true → isDigitChar d ≡ false → (c ≈ᵇ d) ≡ false
digit-≉ {c} d dc dd =
  ¬-not {c ≈ᵇ d} {true} (λ e → contradiction (trans (sym dd) (subst (λ x → isDigitChar x ≡ true) (≈ᵇ⇒≡ {c} {d} e) dc)) (λ ()))

private
  nonzero-not-zero : ∀ {c} → isNonZeroDigit c ≡ true → (c ≈ᵇ '0') ≡ false
  nonzero-not-zero {c} e = not-true (∧-right {isDigitChar c} e)

  nonzero-digit : ∀ {c} → isNonZeroDigit c ≡ true → isDigitChar c ≡ true
  nonzero-digit {c} e = ∧-left {isDigitChar c} e

  digit-not-dash : ∀ {c} → isDigitChar c ≡ true → (c ≈ᵇ '-') ≡ false
  digit-not-dash {c} d = digit-≉ {c} '-' d refl

intPart-nonzero : ∀ pos c cs suffix → isNonZeroDigit c ≡ true → All (λ x → isDigitChar x ≡ true) cs →
  SuffixStops isDigitChar suffix →
  proj₂ (parseIntPart pos ((c ∷ cs) ++ suffix)) ≡ just (mkResult (c ∷ cs) (advancePositions pos (c ∷ cs)) suffix)
intPart-nonzero pos c cs suffix nz ds ss =
  trans (alt-right zero-part nonzero-part pos (c ∷ cs ++ suffix)
          (map-nothing [_] (char '0') pos (c ∷ cs ++ suffix)
            (satisfy-nothing (λ x → x ≈ᵇ '0') pos c (cs ++ suffix) (nonzero-not-zero {c} nz))))
        (ap-just (_∷_ <$> satisfy isNonZeroDigit) (many digit) pos (c ∷ cs ++ suffix)
          (map-just _∷_ (satisfy isNonZeroDigit) pos (c ∷ cs ++ suffix)
            (satisfy-just isNonZeroDigit pos c (cs ++ suffix) nz))
          (manyHelper-satisfy-exhaust-many isDigitChar (advancePosition pos c) cs suffix ds ss))
  where
    zero-part : Parser (List Char)
    zero-part = [_] <$> char '0'
    nonzero-part : Parser (List Char)
    nonzero-part = _∷_ <$> satisfy isNonZeroDigit <*> many digit

-- The digits of a number, read back as the integer part.
parseIntPart-showNat : ∀ pos n suffix → SuffixStops isDigitChar suffix →
  proj₂ (parseIntPart pos (showNat-chars n ++ suffix)) ≡ just (mkResult (showNat-chars n) (advancePositions pos (showNat-chars n)) suffix)
parseIntPart-showNat pos zero suffix _ =
  alt-left ([_] <$> char '0') (_∷_ <$> satisfy isNonZeroDigit <*> many digit) pos ('0' ∷ suffix)
    (map-just [_] (char '0') pos ('0' ∷ suffix) (satisfy-just (λ x → x ≈ᵇ '0') pos '0' suffix refl))
parseIntPart-showNat pos (suc k) suffix ss with lead-fuel (suc k) (suc k) (s≤s z≤n) ≤-refl
                                              | All-digit-fuel (suc (suc k)) (suc k)
... | c , cs , eq , nz | all =
  subst (λ ds → proj₂ (parseIntPart pos (ds ++ suffix)) ≡ just (mkResult ds (advancePositions pos ds) suffix))
        (sym eq) (intPart-nonzero pos c cs suffix nz (tail (subst (All _) eq all)) ss)
  where
    tail : ∀ {x xs} → All (λ y → isDigitChar y ≡ true) (x ∷ xs) → All (λ y → isDigitChar y ≡ true) xs
    tail (_ ∷ t) = t

-- ============================================================================
-- THE VALUE
-- ============================================================================

-- The rational an integer is, as the parser builds it.
intValue : ℤ → ℚ
intValue z = toℚ (fromℤ z)

-- A rational with denominator 1 is the integer it holds.
intValue-mkℚ : ∀ num .(c : Coprime ∣ num ∣ 1) → intValue num ≡ mkℚ num 0 c
intValue-mkℚ (+ zero)    _ = refl
intValue-mkℚ (+ suc _)   _ = refl
intValue-mkℚ -[1+ _ ]    _ = refl

scientific-int : ∀ neg ds → scientificLiteral neg ds [] nothing [] ≡ decimalLiteral neg ds [] (+ 0)
scientific-int neg ds with significand (ds ++ []) in e
... | []    , t = refl
... | _ ∷ _ , t = cong (λ s → signedDecRat neg (rawFromSignificand s 0 0)) e

private
  canon64 : ∀ k → suc k < heldMagnitude →
    canonical (rawLiteral (showNat-chars (suc k) ++ []) 0 0) ≡ (suc k , 0 , 0)
  canon64 k k< with literal-verdict (showNat-chars (suc k) ++ []) 0 0
  ... | exact e = trans e exact-eq
    where
      exact-eq : exactTriple (showNat-chars (suc k) ++ []) 0 0 ≡ (suc k , 0 , 0)
      exact-eq = cong (λ v → (v , 0 , 0))
        (trans (*-identityʳ (foldDigits (showNat-chars (suc k) ++ [])))
               (trans (cong foldDigits (++-identityʳ (showNat-chars (suc k)))) (foldDigits-showNat-chars (suc k))))
  ... | held _ large = ⊥-elim (not-large (subst LargeComponent exact-eq large))
    where
      exact-eq : exactTriple (showNat-chars (suc k) ++ []) 0 0 ≡ (suc k , 0 , 0)
      exact-eq = cong (λ v → (v , 0 , 0))
        (trans (*-identityʳ (foldDigits (showNat-chars (suc k) ++ [])))
               (trans (cong foldDigits (++-identityʳ (showNat-chars (suc k)))) (foldDigits-showNat-chars (suc k))))
      not-large : LargeComponent (suc k , 0 , 0) → ⊥
      not-large (inj₁ big)         = <-irrefl refl (≤-<-trans big k<)
      not-large (inj₂ (s≤s ()))

-- An integer's digits read back to the integer, below 2^64.
bareInt64 : ∀ neg n → n < heldMagnitude →
  decimalLiteral neg (showNat-chars n) [] (+ 0) ≡ canonicalizeDecRat (applySign neg n) 0 0
bareInt64 nothing  zero    _  = refl
bareInt64 (just _) zero    _  = refl
bareInt64 nothing  (suc k) n< = signedDecRat-canon-+ (rawLiteral (showNat-chars (suc k) ++ []) 0 0) k 0 0 _ (canon64 k n<)
bareInt64 (just c) (suc k) n< = signedDecRat-canon-neg (rawLiteral (showNat-chars (suc k) ++ []) 0 0) c k 0 0 _ (canon64 k n<)

int-value : ∀ neg n → n < heldMagnitude → toℚ (scientificLiteral neg (showNat-chars n) [] nothing []) ≡ intValue (applySign neg n)
int-value neg n n< =
  cong toℚ (trans (scientific-int neg (showNat-chars n)) (trans (bareInt64 neg n n<) (canonicalizeDecRat-zero-exp (applySign neg n))))

-- ============================================================================
-- THE NUMBER
-- ============================================================================

-- What follows a number the formatter writes: the end of the text, or a
-- character no part of a number starts with.
data NumberEnd : List Char → Set where
  end-of-text : NumberEnd []
  end-at      : ∀ {c cs} → isDigitChar c ≡ false → (c ≈ᵇ '.') ≡ false → (c ≈ᵇ 'e') ≡ false →
                (c ≈ᵇ 'E') ≡ false → NumberEnd (c ∷ cs)

NumberEnd-digits : ∀ {s} → NumberEnd s → SuffixStops isDigitChar s
NumberEnd-digits end-of-text           = []-stop
NumberEnd-digits (end-at d _ _ _)      = ∷-stop d

private
  frac-none : ∀ pos s → NumberEnd s → proj₂ (optional (char '.' *> digitRun) pos s) ≡ just (mkResult nothing pos s)
  frac-none pos [] _ = refl
  frac-none pos (c ∷ cs) (end-at _ dot _ _) =
    optional-nothing (char '.' *> digitRun) pos (c ∷ cs)
      (bind-nothing (char '.') (λ _ → digitRun) pos (c ∷ cs) (satisfy-nothing (λ x → x ≈ᵇ '.') pos c cs dot))

  exp-none : ∀ pos s → NumberEnd s → proj₂ (optional parseExponent pos s) ≡ just (mkResult nothing pos s)
  exp-none pos [] _ = refl
  exp-none pos (c ∷ cs) (end-at _ _ e E) =
    optional-nothing parseExponent pos (c ∷ cs)
      (ap-nothing (exponentParts <$> (char 'e' <|> char 'E') <*> optional (char '+' <|> char '-')) digitRun pos (c ∷ cs)
        (ap-nothing (exponentParts <$> (char 'e' <|> char 'E')) (optional (char '+' <|> char '-')) pos (c ∷ cs)
          (map-nothing exponentParts (char 'e' <|> char 'E') pos (c ∷ cs)
            (trans (alt-right (char 'e') (char 'E') pos (c ∷ cs) (satisfy-nothing (λ x → x ≈ᵇ 'e') pos c cs e))
                   (satisfy-nothing (λ x → x ≈ᵇ 'E') pos c cs E)))))

  -- After its optional sign, a number's integer part, then nothing more.
  rational-steps : ∀ pos input {neg pos₁} ds suffix →
    proj₂ (optional (char '-') pos input) ≡ just (mkResult neg pos₁ (ds ++ suffix)) →
    proj₂ (parseIntPart pos₁ (ds ++ suffix)) ≡ just (mkResult ds (advancePositions pos₁ ds) suffix) →
    NumberEnd suffix →
    proj₂ (parseRational pos input)
      ≡ just (mkResult (toℚ (scientificLiteral neg ds [] nothing [])) (advancePositions pos₁ ds) suffix)
  rational-steps pos input {neg} {pos₁} ds suffix e₁ e₂ end =
    ap-just (literalValue <$> optional (char '-') <*> parseIntPart <*> optional (char '.' *> digitRun))
            (optional parseExponent) pos input
      (ap-just (literalValue <$> optional (char '-') <*> parseIntPart) (optional (char '.' *> digitRun)) pos input
        (ap-just (literalValue <$> optional (char '-')) parseIntPart pos input
          (map-just literalValue (optional (char '-')) pos input e₁) e₂)
        (frac-none (advancePositions pos₁ ds) suffix end))
      (exp-none (advancePositions pos₁ ds) suffix end)

-- A natural number the formatter writes, read back.
parseRational-nat : ∀ pos n suffix → n < heldMagnitude → NumberEnd suffix →
  proj₂ (parseRational pos (showNat-chars n ++ suffix))
    ≡ just (mkResult (intValue (+ n)) (advancePositions pos (showNat-chars n)) suffix)
parseRational-nat pos n suffix n< end =
  trans (rational-steps pos (showNat-chars n ++ suffix) (showNat-chars n) suffix
          (optional-nothing (char '-') pos (showNat-chars n ++ suffix) (no-dash n))
          (parseIntPart-showNat pos n suffix (NumberEnd-digits end)) end)
        (cong (λ v → just (mkResult v (advancePositions pos (showNat-chars n)) suffix)) (int-value nothing n n<))
  where
    no-dash : ∀ n → proj₂ (char '-' pos (showNat-chars n ++ suffix)) ≡ nothing
    no-dash zero = refl
    no-dash (suc k) with lead-fuel (suc k) (suc k) (s≤s z≤n) ≤-refl
    ... | c , cs , eq , nz =
      subst (λ ds → proj₂ (char '-' pos (ds ++ suffix)) ≡ nothing) (sym eq)
            (satisfy-nothing (λ x → x ≈ᵇ '-') pos c (cs ++ suffix) (digit-not-dash {c} (nonzero-digit {c} nz)))

-- A negative integer the formatter writes, read back.
parseRational-neg : ∀ pos k suffix → suc k < heldMagnitude → NumberEnd suffix →
  proj₂ (parseRational pos ('-' ∷ showNat-chars (suc k) ++ suffix))
    ≡ just (mkResult (intValue -[1+ k ]) (advancePositions pos ('-' ∷ showNat-chars (suc k))) suffix)
parseRational-neg pos k suffix k< end =
  trans (rational-steps pos ('-' ∷ showNat-chars (suc k) ++ suffix) (showNat-chars (suc k)) suffix
          (optional-just (char '-') pos ('-' ∷ showNat-chars (suc k) ++ suffix)
            (satisfy-just (λ x → x ≈ᵇ '-') pos '-' (showNat-chars (suc k) ++ suffix) refl))
          (parseIntPart-showNat (advancePosition pos '-') (suc k) suffix (NumberEnd-digits end)) end)
        (cong (λ v → just (mkResult v (advancePositions pos ('-' ∷ showNat-chars (suc k))) suffix))
              (int-value (just '-') (suc k) k<))

-- Every integer the formatter writes whose magnitude is below 2^64 reads
-- back as itself.
parseNumber-showsℤ : ∀ pos z suffix → ∣ z ∣ < heldMagnitude → NumberEnd suffix →
  proj₂ (parseNumber pos (showsℤ z suffix))
    ≡ just (mkResult (JNumber (intValue z)) (advancePositions pos (intChars z)) suffix)
parseNumber-showsℤ pos (+ n) suffix n< end =
  subst₂ (λ input cs → proj₂ (parseNumber pos input) ≡ just (mkResult (JNumber (intValue (+ n))) (advancePositions pos cs) suffix))
    (sym (showsℕ-chars n suffix)) (sym (trans (showsℕ-chars n []) (++-identityʳ _)))
    (map-just JNumber parseRational pos (showNat-chars n ++ suffix) (parseRational-nat pos n suffix n< end))
parseNumber-showsℤ pos -[1+ k ] suffix k< end =
  subst₂ (λ input cs → proj₂ (parseNumber pos input) ≡ just (mkResult (JNumber (intValue -[1+ k ])) (advancePositions pos cs) suffix))
    (cong ('-' ∷_) (sym (showsℕ-chars (suc k) suffix))) (cong ('-' ∷_) (sym (trans (showsℕ-chars (suc k) []) (++-identityʳ _))))
    (map-just JNumber parseRational pos ('-' ∷ showNat-chars (suc k) ++ suffix) (parseRational-neg pos k suffix k< end))

-- The first character of an integer the formatter writes: `-` or a digit.
number-head : ∀ z r →
  Σ[ c ∈ Char ] Σ[ cs ∈ List Char ] (showsℤ z r ≡ c ∷ cs × (c ≡ '-' ⊎ isDigitChar c ≡ true))
number-head -[1+ k ]  r = '-' , showsℕ (suc k) r , refl , inj₁ refl
number-head (+ zero)  r = '0' , r , refl , inj₂ refl
number-head (+ suc k) r with lead-fuel (suc k) (suc k) (s≤s z≤n) ≤-refl
... | c , cs , eq , nz = c , cs ++ r , trans (showsℕ-chars (suc k) r) (cong (_++ r) eq) , inj₂ (nonzero-digit {c} nz)
