-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- The JSON parser accepts only RFC 8259 JSON text: whatever input
-- `parseJSON` reads whole is a `JSONText` of `Aletheia.Protocol.JSON.RFC8259`.
module Aletheia.Protocol.JSON.Properties.Sound where

open import Data.Bool using (Bool; true; false; not; _∧_)
import Data.Bool
open import Data.Char using (Char; _≈ᵇ_)
open import Data.Char.Base using (toℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; suc; _<_; _≤_; _<ᵇ_)
open import Data.Nat.Properties using (<ᵇ⇒<; ≤-pred)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import Aletheia.Parser.Combinators using (_<|>_; _*>_; satisfy; char; anyChar; many; optional)
open import Aletheia.Parser.Properties.Chars using (∧-left; ∧-right; not-true; ∨-cases; ≈ᵇ⇒≡; ≈ᵇ-false; any-≈ᵇ)
open import Aletheia.Parser.Properties.Sound using (Accepts; Sound; Star; _·_; _⨾_; accepts-alt; accepts-ap; accepts-before; accepts-bind; accepts-map; accepts-or; accepts-then; accepts-weaken; before-eof; bind-sound; char-sound; fail-sound; if-accepts; many-sound; optional-sound; pure-sound; satisfy-sound; star-more; star-none; star-satisfy; string-sound; then-sound; weaken)
open import Aletheia.Protocol.JSON.Parse using (decodeEscape; digit; digitRun; hex4; hexDigit; isDigitChar; isHexDigit; isHighSurrogate; isLowSurrogate; isNonZeroDigit; isUnescaped; isWhitespace; lookupᶜ; lowSurrogate; parseArray; parseBoolean; parseEscape; parseExponent; parseIntPart; parseJSON; parseMember; parseMembers; parseNull; parseNumber; parseObject; parseString; parseStringChar; parseStringChars; parseValue; parseValues; shortEscapes; structural; unicodeEscape; whitespace; ws)
open import Aletheia.Protocol.JSON.RFC8259 using (Digit; E; HexDig; Int; JSONText; Member; Members; MoreMembers; MoreValues; Number; OptExp; OptFrac; OptMinus; OptSign; StringChar; StringChars; StringLit; Structural; Unescaped; Value; Values; Ws; WsChar; char-backslash; char-backspace; char-formfeed; char-linefeed; char-quote; char-return; char-solidus; char-tab; char-unescaped; char-unicode; chars-more; chars-none; e-lower; e-upper; exp; frac; int-nonzero; int-zero; json-text; member; members-none; members-some; minus; more-members; more-members-none; more-values; more-values-none; no-exp; no-frac; no-minus; no-sign; number; sign-minus; sign-plus; string-lit; structural-ws; value-array; value-false; value-null; value-number; value-object; value-string; value-true; values-none; values-some; ws-cr; ws-lf; ws-space; ws-tab)
open import Aletheia.Protocol.JSON.Types using (JSON; JNull; JBool)

-- ============================================================================
-- CHARACTER TESTS
-- ============================================================================

private
  T-<ᵇ : ∀ {m n} → (m <ᵇ n) ≡ true → m < n
  T-<ᵇ {m} {n} eq = <ᵇ⇒< m n (subst Data.Bool.T (sym eq) tt)

  -- Both bounds of a range test on a character's code.
  range : ∀ lo hi c → ((lo <ᵇ toℕ c) ∧ (toℕ c <ᵇ suc hi)) ≡ true → suc lo ≤ toℕ c × toℕ c ≤ hi
  range lo hi c eq = T-<ᵇ (∧-left eq) , ≤-pred (T-<ᵇ (∧-right {lo <ᵇ toℕ c} eq))

ws-member : ∀ {c} → c ∈ whitespace → WsChar c
ws-member (here refl)                         = ws-space
ws-member (there (here refl))                 = ws-tab
ws-member (there (there (here refl)))         = ws-lf
ws-member (there (there (there (here refl)))) = ws-cr
ws-member (there (there (there (there ()))))

isWhitespace-ws : ∀ c → isWhitespace c ≡ true → WsChar c
isWhitespace-ws c eq = ws-member (any-≈ᵇ c whitespace eq)

isDigitChar-digit : ∀ c → isDigitChar c ≡ true → Digit c
isDigitChar-digit c = range 47 57 c

isNonZeroDigit-digit : ∀ c → isNonZeroDigit c ≡ true → Digit c × c ≢ '0'
isNonZeroDigit-digit c eq =
  isDigitChar-digit c (∧-left eq) , ≈ᵇ-false (not-true (∧-right {isDigitChar c} eq))

isUnescaped-unescaped : ∀ c → isUnescaped c ≡ true → Unescaped c
isUnescaped-unescaped c eq =
  T-<ᵇ (∧-left eq) ,
  ≈ᵇ-false (not-true (∧-left (∧-right {31 <ᵇ toℕ c} eq))) ,
  ≈ᵇ-false (not-true (∧-right {not (c ≈ᵇ '"')} (∧-right {31 <ᵇ toℕ c} eq)))

isHexDigit-hexdig : ∀ c → isHexDigit c ≡ true → HexDig c
isHexDigit-hexdig c eq =
  Sum.map (isDigitChar-digit c) (Sum.swap ∘ Sum.map (range 96 102 c) (range 64 70 c) ∘ ∨-cases)
          (∨-cases {isDigitChar c} eq)

-- A key a table lookup finds, with the value found, is a pair of the table.
lookupᶜ-∈ : ∀ c kvs {v} → lookupᶜ c kvs ≡ just v → (c , v) ∈ kvs
lookupᶜ-∈ c ((k , w) ∷ kvs) e with c ≈ᵇ k in e′
... | true  = here (cong₂ _,_ (≈ᵇ⇒≡ e′) (sym (just-injective e)))
... | false = there (lookupᶜ-∈ c kvs e)

-- Every one-character escape the parser reads is one of the grammar's.
escape-char : ∀ {c d} → (c , d) ∈ shortEscapes → StringChar ('\\' ∷ c ∷ [])
escape-char (here refl)                                                         = char-quote
escape-char (there (here refl))                                                 = char-backslash
escape-char (there (there (here refl)))                                         = char-solidus
escape-char (there (there (there (here refl))))                                 = char-backspace
escape-char (there (there (there (there (here refl)))))                         = char-formfeed
escape-char (there (there (there (there (there (here refl))))))                 = char-linefeed
escape-char (there (there (there (there (there (there (here refl)))))))         = char-return
escape-char (there (there (there (there (there (there (there (here refl)))))))) = char-tab
escape-char (there (there (there (there (there (there (there (there ()))))))))

-- ============================================================================
-- WHITESPACE, LITERALS
-- ============================================================================

ws-sound : Accepts ws Ws
ws-sound = weaken conv (many-sound (satisfy-sound isWhitespace))
  where
    conv : ∀ {cs vs} → Star (λ xs c → xs ≡ c ∷ [] × isWhitespace c ≡ true) cs vs → Ws cs
    conv s = All.map (λ {c} → isWhitespace-ws c) (proj₂ (star-satisfy s))

structural-sound : ∀ s → Accepts (structural s) (Structural s)
structural-sound s = accepts-weaken conv (accepts-before (accepts-then ws-sound (weaken proj₁ (char-sound s))) ws-sound)
  where
    conv : ∀ {cs} → ((Ws · (λ xs → xs ≡ s ∷ [])) · Ws) cs → Structural s cs
    conv (.(a ++ s ∷ []) , b , refl , (a , .(s ∷ []) , refl , wa , refl) , wb) =
      subst (Structural s) (sym (++-assoc a (s ∷ []) b)) (structural-ws wa wb)

parseNull-sound : Accepts parseNull Value
parseNull-sound = accepts-weaken conv (accepts-bind (string-sound "null") (λ _ → weaken proj₁ (pure-sound JNull)))
  where
    conv : ∀ {cs} → ((λ xs → xs ≡ 'n' ∷ 'u' ∷ 'l' ∷ 'l' ∷ []) · (λ ys → ys ≡ [])) cs → Value cs
    conv (_ , _ , refl , refl , refl) = value-null

parseBoolean-sound : Accepts parseBoolean Value
parseBoolean-sound = accepts-or
  (accepts-weaken conv-true (accepts-bind (string-sound "true") (λ _ → weaken proj₁ (pure-sound (JBool true)))))
  (accepts-weaken conv-false (accepts-bind (string-sound "false") (λ _ → weaken proj₁ (pure-sound (JBool false)))))
  where
    conv-true : ∀ {cs} → ((λ xs → xs ≡ 't' ∷ 'r' ∷ 'u' ∷ 'e' ∷ []) · (λ ys → ys ≡ [])) cs → Value cs
    conv-true (_ , _ , refl , refl , refl) = value-true
    conv-false : ∀ {cs} → ((λ xs → xs ≡ 'f' ∷ 'a' ∷ 'l' ∷ 's' ∷ 'e' ∷ []) · (λ ys → ys ≡ [])) cs → Value cs
    conv-false (_ , _ , refl , refl , refl) = value-false

-- ============================================================================
-- NUMBERS
-- ============================================================================

digit-sound : Accepts digit (λ cs → Σ[ c ∈ Char ] (cs ≡ c ∷ [] × Digit c))
digit-sound = weaken (λ { {_} {c} (refl , d) → c , refl , isDigitChar-digit c d }) (satisfy-sound isDigitChar)

digits-sound : Accepts (many digit) (All Digit)
digits-sound = weaken conv (many-sound (satisfy-sound isDigitChar))
  where
    conv : ∀ {cs vs} → Star (λ xs c → xs ≡ c ∷ [] × isDigitChar c ≡ true) cs vs → All Digit cs
    conv s = All.map (λ {c} → isDigitChar-digit c) (proj₂ (star-satisfy s))

-- One digit, then digits.
Digits1 : List Char → Set
Digits1 cs = Σ[ c ∈ Char ] Σ[ ds ∈ List Char ] (cs ≡ c ∷ ds × Digit c × All Digit ds)

digitRun-sound : Accepts digitRun Digits1
digitRun-sound = accepts-weaken conv (accepts-ap (accepts-map digit-sound) digits-sound)
  where
    conv : ∀ {cs} → ((λ xs → Σ[ c ∈ Char ] (xs ≡ c ∷ [] × Digit c)) · All Digit) cs → Digits1 cs
    conv (_ , ds , refl , (c , refl , d) , all) = c , ds , refl , d , all

parseIntPart-sound : Accepts parseIntPart Int
parseIntPart-sound = accepts-or
  (accepts-weaken conv-zero (accepts-map (weaken proj₁ (char-sound '0'))))
  (accepts-weaken conv-nonzero (accepts-ap (accepts-map nonzero) digits-sound))
  where
    nonzero : Accepts (satisfy isNonZeroDigit) (λ cs → Σ[ c ∈ Char ] (cs ≡ c ∷ [] × Digit c × c ≢ '0'))
    nonzero = weaken (λ { {_} {c} (refl , n) → c , refl , isNonZeroDigit-digit c n }) (satisfy-sound isNonZeroDigit)
    conv-zero : ∀ {cs} → cs ≡ '0' ∷ [] → Int cs
    conv-zero refl = int-zero
    conv-nonzero : ∀ {cs} → ((λ xs → Σ[ c ∈ Char ] (xs ≡ c ∷ [] × Digit c × c ≢ '0')) · All Digit) cs → Int cs
    conv-nonzero (_ , _ , refl , (c , refl , d , nz) , all) = int-nonzero d nz all

optMinus-sound : Accepts (optional (char '-')) OptMinus
optMinus-sound = weaken conv (optional-sound (char-sound '-'))
  where
    conv : ∀ {cs m} → (cs ≡ [] × m ≡ nothing) ⊎ Σ[ c ∈ Char ] ((cs ≡ '-' ∷ [] × c ≡ '-') × m ≡ just c) → OptMinus cs
    conv (inj₁ (refl , _))           = no-minus
    conv (inj₂ (_ , (refl , _) , _)) = minus

optFrac-sound : Accepts (optional (char '.' *> digitRun)) OptFrac
optFrac-sound = weaken conv (optional-sound (accepts-then (weaken proj₁ (char-sound '.')) digitRun-sound))
  where
    conv : ∀ {cs m} → (cs ≡ [] × m ≡ nothing) ⊎ Σ[ ds ∈ List Char ] (((λ xs → xs ≡ '.' ∷ []) · Digits1) cs × m ≡ just ds) →
      OptFrac cs
    conv (inj₁ (refl , _)) = no-frac
    conv (inj₂ (_ , (_ , _ , refl , refl , (c , ds , refl , d , all)) , _)) = frac d all

optSign-sound : Accepts (optional (char '+' <|> char '-')) OptSign
optSign-sound = weaken conv (optional-sound (accepts-alt (weaken proj₁ (char-sound '+')) (weaken proj₁ (char-sound '-'))))
  where
    conv : ∀ {cs m} → (cs ≡ [] × m ≡ nothing) ⊎ Σ[ c ∈ Char ] ((cs ≡ '+' ∷ [] ⊎ cs ≡ '-' ∷ []) × m ≡ just c) → OptSign cs
    conv (inj₁ (refl , _))          = no-sign
    conv (inj₂ (_ , inj₁ refl , _)) = sign-plus
    conv (inj₂ (_ , inj₂ refl , _)) = sign-minus

e-sound : Accepts (char 'e' <|> char 'E') (λ cs → Σ[ c ∈ Char ] (cs ≡ c ∷ [] × E c))
e-sound = accepts-weaken conv (accepts-alt (weaken proj₁ (char-sound 'e')) (weaken proj₁ (char-sound 'E')))
  where
    conv : ∀ {cs} → cs ≡ 'e' ∷ [] ⊎ cs ≡ 'E' ∷ [] → Σ[ c ∈ Char ] (cs ≡ c ∷ [] × E c)
    conv (inj₁ refl) = 'e' , refl , e-lower
    conv (inj₂ refl) = 'E' , refl , e-upper

parseExponent-sound : Accepts parseExponent OptExp
parseExponent-sound = accepts-weaken conv (accepts-ap (accepts-ap (accepts-map e-sound) optSign-sound) digitRun-sound)
  where
    conv : ∀ {cs} → (((λ xs → Σ[ c ∈ Char ] (xs ≡ c ∷ [] × E c)) · OptSign) · Digits1) cs → OptExp cs
    conv (_ , _ , refl , (_ , s , refl , (e , refl , ee) , os) , (c , ds , refl , d , all)) = exp ee os d all

optExp-sound : Accepts (optional parseExponent) OptExp
optExp-sound = weaken conv (optional-sound parseExponent-sound)
  where
    conv : ∀ {cs m} → (cs ≡ [] × m ≡ nothing) ⊎ Σ[ x ∈ (Maybe Char × List Char) ] (OptExp cs × m ≡ just x) → OptExp cs
    conv (inj₁ (refl , _)) = no-exp
    conv (inj₂ (_ , x , _)) = x

parseNumber-sound : Accepts parseNumber Value
parseNumber-sound = accepts-map (accepts-weaken conv
  (accepts-ap (accepts-ap (accepts-ap (accepts-map optMinus-sound) parseIntPart-sound) optFrac-sound) optExp-sound))
  where
    conv : ∀ {cs} → (((OptMinus · Int) · OptFrac) · OptExp) cs → Value cs
    conv (_ , x , refl , (_ , f , refl , (m , i , refl , om , ii) , of) , ox) =
      value-number (subst Number (lemma m i f x) (number om ii of ox))
      where
        lemma : ∀ m i f x → m ++ i ++ f ++ x ≡ ((m ++ i) ++ f) ++ x
        lemma m i f x = trans (sym (++-assoc m i (f ++ x))) (sym (++-assoc (m ++ i) f x))

-- ============================================================================
-- STRINGS
-- ============================================================================

StringChars-++ : ∀ {xs ys} → StringChars xs → StringChars ys → StringChars (xs ++ ys)
StringChars-++ chars-none ys = ys
StringChars-++ {ys = zs} (chars-more {c} {cs} sc s) ys =
  subst StringChars (sym (++-assoc c cs zs)) (chars-more sc (StringChars-++ s ys))

-- Four hex digits.
Hex4 : List Char → Set
Hex4 cs = Σ[ h₁ ∈ Char ] Σ[ h₂ ∈ Char ] Σ[ h₃ ∈ Char ] Σ[ h₄ ∈ Char ]
  (cs ≡ h₁ ∷ h₂ ∷ h₃ ∷ h₄ ∷ [] × HexDig h₁ × HexDig h₂ × HexDig h₃ × HexDig h₄)

hexDigit-sound : Accepts hexDigit (λ cs → Σ[ c ∈ Char ] (cs ≡ c ∷ [] × HexDig c))
hexDigit-sound = accepts-map (weaken (λ { {_} {c} (refl , h) → c , refl , isHexDigit-hexdig c h }) (satisfy-sound isHexDigit))

hex4-sound : Accepts hex4 Hex4
hex4-sound = accepts-weaken conv
  (accepts-ap (accepts-ap (accepts-ap (accepts-map hexDigit-sound) hexDigit-sound) hexDigit-sound) hexDigit-sound)
  where
    H : List Char → Set
    H cs = Σ[ c ∈ Char ] (cs ≡ c ∷ [] × HexDig c)
    conv : ∀ {cs} → (((H · H) · H) · H) cs → Hex4 cs
    conv (_ , _ , refl , (_ , _ , refl , (_ , _ , refl , (h₁ , refl , x₁) , (h₂ , refl , x₂)) , (h₃ , refl , x₃)) ,
          (h₄ , refl , x₄)) = h₁ , h₂ , h₃ , h₄ , refl , x₁ , x₂ , x₃ , x₄

-- A low surrogate's escape: `\u` and four hex digits.
LowTail : List Char → Set
LowTail cs = Σ[ hs ∈ List Char ] (cs ≡ '\\' ∷ 'u' ∷ hs × Hex4 hs)

lowSurrogate-sound : ∀ high → Accepts (lowSurrogate high) LowTail
lowSurrogate-sound high = accepts-weaken conv
  (accepts-bind (accepts-then (accepts-then (weaken proj₁ (char-sound '\\')) (weaken proj₁ (char-sound 'u'))) hex4-sound)
                (λ low → if-accepts (isLowSurrogate low) (weaken proj₁ (pure-sound _)) (weaken (λ ()) fail-sound)))
  where
    conv : ∀ {cs} → ((((λ xs → xs ≡ '\\' ∷ []) · (λ xs → xs ≡ 'u' ∷ [])) · Hex4) · (λ ys → ys ≡ [])) cs → LowTail cs
    conv (_ , _ , refl , (_ , hs , refl , (_ , _ , refl , refl , refl) , h) , refl) =
      hs , cong (λ z → '\\' ∷ 'u' ∷ z) (++-identityʳ hs) , h

unicodeEscape-sound : Accepts unicodeEscape (λ ys → StringChars ('\\' ∷ 'u' ∷ ys))
unicodeEscape-sound = accepts-weaken conv
  (accepts-bind hex4-sound (λ unit →
     if-accepts (isHighSurrogate unit) (accepts-weaken inj₂ (lowSurrogate-sound unit))
       (if-accepts (isLowSurrogate unit) (weaken (λ ()) fail-sound) (accepts-weaken inj₁ (weaken proj₁ (pure-sound _))))))
  where
    conv : ∀ {cs} → (Hex4 · (λ ys → ys ≡ [] ⊎ LowTail ys)) cs → StringChars ('\\' ∷ 'u' ∷ cs)
    conv (_ , _ , refl , (h₁ , h₂ , h₃ , h₄ , refl , x₁ , x₂ , x₃ , x₄) , inj₁ refl) =
      chars-more (char-unicode x₁ x₂ x₃ x₄) chars-none
    conv (_ , _ , refl , (h₁ , h₂ , h₃ , h₄ , refl , x₁ , x₂ , x₃ , x₄) ,
          inj₂ (_ , refl , (k₁ , k₂ , k₃ , k₄ , refl , y₁ , y₂ , y₃ , y₄))) =
      chars-more (char-unicode x₁ x₂ x₃ x₄) (chars-more (char-unicode y₁ y₂ y₃ y₄) chars-none)

decodeEscape-sound : ∀ c → Accepts (decodeEscape c) (λ ys → StringChars ('\\' ∷ c ∷ ys))
decodeEscape-sound c with c ≈ᵇ 'u' in e
... | true = subst (λ x → Accepts unicodeEscape (λ ys → StringChars ('\\' ∷ x ∷ ys))) (sym (≈ᵇ⇒≡ e)) unicodeEscape-sound
... | false with lookupᶜ c shortEscapes in e₂
...   | nothing = weaken (λ ()) fail-sound
...   | just d  =
  weaken (λ { (refl , _) → chars-more (escape-char (lookupᶜ-∈ c shortEscapes e₂)) chars-none }) (pure-sound d)

parseEscape-sound : Accepts parseEscape StringChars
parseEscape-sound = weaken (λ {cs} {v} → conv {cs} {v}) body
  where
    Introduced : List Char → Char → Set
    Introduced xs c = xs ≡ '\\' ∷ c ∷ []
    Escaped : Char → List Char → Char → Set
    Escaped c ys _ = StringChars ('\\' ∷ c ∷ ys)
    introducer : Sound (char '\\' *> anyChar) Introduced
    introducer = weaken (λ { (_ , _ , _ , refl , (refl , _) , (refl , _)) → refl })
                        (then-sound (char-sound '\\') (satisfy-sound (λ _ → true)))
    body : Sound parseEscape (Introduced ⨾ Escaped)
    body = bind-sound introducer decodeEscape-sound
    conv : ∀ {cs} {v : Char} → (Introduced ⨾ Escaped) cs v → StringChars cs
    conv (_ , _ , _ , refl , refl , s) = s

parseStringChar-sound : Accepts parseStringChar StringChars
parseStringChar-sound = accepts-or parseEscape-sound
  (weaken (λ { {_} {c} (refl , u) → chars-more (char-unescaped (isUnescaped-unescaped c u)) chars-none }) (satisfy-sound isUnescaped))

parseStringChars-sound : Accepts parseStringChars StringLit
parseStringChars-sound = accepts-weaken conv
  (accepts-before (accepts-then (weaken proj₁ (char-sound '"')) (weaken body (many-sound parseStringChar-sound)))
                  (weaken proj₁ (char-sound '"')))
  where
    body : ∀ {cs vs} → Star (λ cs _ → StringChars cs) cs vs → StringChars cs
    body star-none = chars-none
    body (star-more s rest) = StringChars-++ s (body rest)
    conv : ∀ {cs} → (((λ xs → xs ≡ '"' ∷ []) · StringChars) · (λ xs → xs ≡ '"' ∷ [])) cs → StringLit cs
    conv (_ , _ , refl , (_ , _ , refl , refl , s) , refl) = string-lit s

parseString-sound : Accepts parseString Value
parseString-sound = accepts-map (accepts-weaken value-string parseStringChars-sound)

-- ============================================================================
-- VALUES
-- ============================================================================

private
  assoc₃ : ∀ (a b c : List Char) → a ++ b ++ c ≡ (a ++ b) ++ c
  assoc₃ a b c = sym (++-assoc a b c)

mutual
  parseValue-sound : ∀ b → Accepts (parseValue b) Value
  parseValue-sound []      = weaken (λ ()) fail-sound
  parseValue-sound (_ ∷ b) =
    accepts-or (accepts-or (accepts-or (accepts-or (accepts-or parseNull-sound parseBoolean-sound)
      parseNumber-sound) parseString-sound) (parseArray-sound b)) (parseObject-sound b)

  parseArray-sound : ∀ b → Accepts (parseArray b) Value
  parseArray-sound b = accepts-weaken conv
    (accepts-before (accepts-then (structural-sound '[')
                                  (accepts-map (accepts-or (parseValues-sound b) (weaken (λ { (refl , _) → values-none }) (pure-sound [])))))
                    (structural-sound ']'))
    where
      conv : ∀ {cs} → ((Structural '[' · Values) · Structural ']') cs → Value cs
      conv (_ , e , refl , (o , vs , refl , so , v) , se) = subst Value (assoc₃ o vs e) (value-array so v se)

  parseValues-sound : ∀ b → Accepts (parseValues b) Values
  parseValues-sound b = accepts-weaken conv (accepts-ap (accepts-map (parseValue-sound b)) (moreValues-sound b))
    where
      conv : ∀ {cs} → (Value · MoreValues) cs → Values cs
      conv (_ , _ , refl , v , m) = values-some v m

  moreValues-sound : ∀ b → Accepts (many (structural ',' *> parseValue b)) MoreValues
  moreValues-sound b = weaken conv (many-sound (accepts-then (structural-sound ',') (parseValue-sound b)))
    where
      conv : ∀ {cs vs} → Star (λ cs _ → (Structural ',' · Value) cs) cs vs → MoreValues cs
      conv star-none = more-values-none
      conv (star-more (s , v , refl , ss , sv) rest) = subst MoreValues (assoc₃ s v _) (more-values ss sv (conv rest))

  parseObject-sound : ∀ b → Accepts (parseObject b) Value
  parseObject-sound b = accepts-weaken conv
    (accepts-before (accepts-then (structural-sound '{')
                                  (accepts-map (accepts-or (parseMembers-sound b) (weaken (λ { (refl , _) → members-none }) (pure-sound [])))))
                    (structural-sound '}'))
    where
      conv : ∀ {cs} → ((Structural '{' · Members) · Structural '}') cs → Value cs
      conv (_ , e , refl , (o , ms , refl , so , m) , se) = subst Value (assoc₃ o ms e) (value-object so m se)

  parseMembers-sound : ∀ b → Accepts (parseMembers b) Members
  parseMembers-sound b = accepts-weaken conv (accepts-ap (accepts-map (parseMember-sound b)) (moreMembers-sound b))
    where
      conv : ∀ {cs} → (Member · MoreMembers) cs → Members cs
      conv (_ , _ , refl , m , ms) = members-some m ms

  moreMembers-sound : ∀ b → Accepts (many (structural ',' *> parseMember b)) MoreMembers
  moreMembers-sound b = weaken conv (many-sound (accepts-then (structural-sound ',') (parseMember-sound b)))
    where
      conv : ∀ {cs vs} → Star (λ cs _ → (Structural ',' · Member) cs) cs vs → MoreMembers cs
      conv star-none = more-members-none
      conv (star-more (s , m , refl , ss , sm) rest) = subst MoreMembers (assoc₃ s m _) (more-members ss sm (conv rest))

  parseMember-sound : ∀ b → Accepts (parseMember b) Member
  parseMember-sound b = accepts-weaken conv
    (accepts-ap (accepts-map (accepts-before parseStringChars-sound (structural-sound ':'))) (parseValue-sound b))
    where
      conv : ∀ {cs} → ((StringLit · Structural ':') · Value) cs → Member cs
      conv (_ , v , refl , (k , s , refl , sk , ss) , sv) = subst Member (assoc₃ k s v) (member sk ss sv)

-- ============================================================================
-- THE WHOLE TEXT
-- ============================================================================

-- Whatever `parseJSON` reads whole is RFC 8259 JSON text.
parseJSON-sound : ∀ pos input r → proj₂ (parseJSON pos input) ≡ just r → JSONText input
parseJSON-sound pos input =
  before-eof (accepts-weaken conv (accepts-before (accepts-then ws-sound (parseValue-sound input)) ws-sound)) pos input
  where
    conv : ∀ {cs} → ((Ws · Value) · Ws) cs → JSONText cs
    conv (_ , b , refl , (a , v , refl , wa , vv) , wb) = subst JSONText (assoc₃ a v b) (json-text wa vv wb)
