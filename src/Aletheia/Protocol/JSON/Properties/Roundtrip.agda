-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- The JSON parser reads back what the formatter writes.
--
-- For a value whose numbers have their numerator magnitude and denominator
-- below 2^64, `parseJSON` reads `formatJSONChars j` whole, back to
-- `wire (rekey j)`: each key as `fromList (toList k)`, which `--safe` cannot
-- reduce for an open `k`, and each rational with a denominator above 1 as
-- the two-field object the formatter writes for it.
module Aletheia.Protocol.JSON.Properties.Roundtrip where

open import Data.Bool using (Bool; true; false)
import Data.Bool
import Data.Char.Base
import Data.Nat.Properties
open import Data.Char using (Char; _≈ᵇ_)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ; +_; -[1+_]; ∣_∣)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.List.Properties using (++-assoc; ++-identityʳ; length-++)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive; ≤-pred; m≤m+n; m≤n+m; <ᵇ⇒<)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Rational using (ℚ; mkℚ)
open import Data.String using (String; toList; fromList)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Aletheia.Parser.Combinators using (Parser; mkResult; advancePositions; char; satisfy; many; pure; string; parseCharsSeq; eof; _>>=_; _<$>_; _<|>_; _*>_; _<*_)
open import Aletheia.Parser.Properties.Success using (Reads; ReadsText; alt-left-reads; alt-right; alt-right-reads; ap-reads; before-reads; bind-nothing; encodeAll; many-reads; map-reads; pure-reads; reading; reads-from; reads-more; reads-none; reads-text; reads-value; readsAt; satisfy-just; satisfy-nothing; then-reads)
open import Aletheia.Parser.Properties.Chars using (≈ᵇ-refl; any-≈ᵇ)
open import Data.Bool.Properties using (¬-not)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Aletheia.DBC.DecRat.Literal using (heldMagnitude)
open import Aletheia.Protocol.JSON.Types using (JSON; JNull; JBool; JNumber; JString; JArray; JObject; NumbersSatisfy; ListNumbersSatisfy; FieldsNumbersSatisfy)
open import Aletheia.Protocol.JSON.Format using (escapeChar; escapeOnto; showsJSON; showsElements; showsFields; showsField; showsString; showsℤ; showsℕ; showsRational; formatJSONChars)
open import Aletheia.Protocol.JSON.Parse using (_<$_; ws; whitespace; isWhitespace; isDigitChar; structural; parseNull; parseBoolean; parseNumber; parseString; parseStringChars; parseValue; parseArray; parseValues; parseObject; parseMembers; parseMember; memberOf; parseJSON)
open import Aletheia.Protocol.JSON.Properties.Roundtrip.Number using (intValue; intValue-mkℚ; showsℕ-chars; showsℤ-chars; NumberEnd; end-of-text; end-at; parseNumber-showsℤ; number-head; digit-≉)
open import Aletheia.Protocol.JSON.Properties.Roundtrip.String using (escapeChar-split; showsString-readback)

-- ============================================================================
-- WHAT THE PARSER GIVES BACK
-- ============================================================================

-- A rational whose numerator magnitude and denominator are below 2^64, the
-- range the parser reads exactly.
ReadExactly : ℚ → Set
ReadExactly (mkℚ num d _) = ∣ num ∣ < heldMagnitude × suc d < heldMagnitude

-- Each key as the parser builds it from the key's characters.
mutual
  rekey : JSON → JSON
  rekey JNull        = JNull
  rekey (JBool b)    = JBool b
  rekey (JNumber q)  = JNumber q
  rekey (JString cs) = JString cs
  rekey (JArray xs)  = JArray (rekeyElements xs)
  rekey (JObject fs) = JObject (rekeyFields fs)

  rekeyElements : List JSON → List JSON
  rekeyElements []       = []
  rekeyElements (x ∷ xs) = rekey x ∷ rekeyElements xs

  rekeyFields : List (String × JSON) → List (String × JSON)
  rekeyFields []             = []
  rekeyFields ((k , v) ∷ fs) = (fromList (toList k) , rekey v) ∷ rekeyFields fs

-- Each rational with a denominator above 1 as the object the formatter
-- writes for it.
mutual
  wire : JSON → JSON
  wire JNull                          = JNull
  wire (JBool b)                      = JBool b
  wire (JNumber (mkℚ num zero c))     = JNumber (mkℚ num zero c)
  wire (JNumber (mkℚ num (suc d) _))  =
    JObject (("numerator" , JNumber (intValue num)) ∷ ("denominator" , JNumber (intValue (+ suc (suc d)))) ∷ [])
  wire (JString cs)                   = JString cs
  wire (JArray xs)                    = JArray (wireElements xs)
  wire (JObject fs)                   = JObject (wireFields fs)

  wireElements : List JSON → List JSON
  wireElements []       = []
  wireElements (x ∷ xs) = wire x ∷ wireElements xs

  wireFields : List (String × JSON) → List (String × JSON)
  wireFields []             = []
  wireFields ((k , v) ∷ fs) = (k , wire v) ∷ wireFields fs

-- Both at once, the form the proof follows.
mutual
  readBack : JSON → JSON
  readBack JNull                         = JNull
  readBack (JBool b)                     = JBool b
  readBack (JNumber (mkℚ num zero c))    = JNumber (intValue num)
  readBack (JNumber (mkℚ num (suc d) _)) =
    JObject (("numerator" , JNumber (intValue num)) ∷ ("denominator" , JNumber (intValue (+ suc (suc d)))) ∷ [])
  readBack (JString cs)                  = JString cs
  readBack (JArray xs)                   = JArray (readBackElements xs)
  readBack (JObject fs)                  = JObject (readBackFields fs)

  readBackElements : List JSON → List JSON
  readBackElements []       = []
  readBackElements (x ∷ xs) = readBack x ∷ readBackElements xs

  readBackFields : List (String × JSON) → List (String × JSON)
  readBackFields []             = []
  readBackFields ((k , v) ∷ fs) = (fromList (toList k) , readBack v) ∷ readBackFields fs

mutual
  readBack-wire-rekey : ∀ j → readBack j ≡ wire (rekey j)
  readBack-wire-rekey JNull                         = refl
  readBack-wire-rekey (JBool b)                     = refl
  readBack-wire-rekey (JNumber (mkℚ num zero c))    = cong JNumber (intValue-mkℚ num c)
  readBack-wire-rekey (JNumber (mkℚ num (suc d) _)) = refl
  readBack-wire-rekey (JString cs)                  = refl
  readBack-wire-rekey (JArray xs)                   = cong JArray (elements xs)
  readBack-wire-rekey (JObject fs)                  = cong JObject (fields fs)

  private
    elements : ∀ xs → readBackElements xs ≡ wireElements (rekeyElements xs)
    elements []       = refl
    elements (x ∷ xs) = cong₂ _∷_ (readBack-wire-rekey x) (elements xs)

    fields : ∀ fs → readBackFields fs ≡ wireFields (rekeyFields fs)
    fields []             = refl
    fields ((k , v) ∷ fs) = cong₂ (λ v′ fs′ → (fromList (toList k) , v′) ∷ fs′) (readBack-wire-rekey v) (fields fs)

-- ============================================================================
-- THE FORMATTER'S OUTPUT, SPLIT FROM WHAT FOLLOWS IT
-- ============================================================================

-- A writer that puts the same characters in front of whatever follows.
AppendLike : (List Char → List Char) → Set
AppendLike P = ∀ r → P r ≡ P [] ++ r

∘-append : ∀ (P Q : List Char → List Char) → AppendLike P → AppendLike Q → AppendLike (λ r → P (Q r))
∘-append P Q p q r =
  trans (cong P (q r)) (trans (p (Q [] ++ r)) (trans (sym (++-assoc (P []) (Q []) r)) (cong (_++ r) (sym (p (Q []))))))

cons-append : ∀ c → AppendLike (c ∷_)
cons-append c r = refl

escapeOnto-split : ∀ cs → AppendLike (escapeOnto cs)
escapeOnto-split []       r = refl
escapeOnto-split (c ∷ cs) r = ∘-append (escapeChar c) (escapeOnto cs) (escapeChar-split c) (escapeOnto-split cs) r

showsString-split : ∀ cs → AppendLike (showsString cs)
showsString-split cs =
  ∘-append ('"' ∷_) (λ r → escapeOnto cs ('"' ∷ r)) (cons-append '"')
           (∘-append (escapeOnto cs) ('"' ∷_) (escapeOnto-split cs) (cons-append '"'))

showsℕ-split : ∀ n → AppendLike (showsℕ n)
showsℕ-split n r = trans (showsℕ-chars n r) (cong (_++ r) (sym (trans (showsℕ-chars n []) (++-identityʳ _))))

showsℤ-split : ∀ z → AppendLike (showsℤ z)
showsℤ-split z = showsℤ-chars z

showsRational-split : ∀ q → AppendLike (showsRational q)
showsRational-split (mkℚ num zero _)    = showsℤ-split num
showsRational-split (mkℚ num (suc d) _) =
  ∘-append ('{' ∷_) _ (cons-append '{')
  (∘-append (showsString (toList "numerator")) _ (showsString-split (toList "numerator"))
  (∘-append (':' ∷_) _ (cons-append ':') (∘-append (' ' ∷_) _ (cons-append ' ')
  (∘-append (showsℤ num) _ (showsℤ-split num)
  (∘-append (',' ∷_) _ (cons-append ',') (∘-append (' ' ∷_) _ (cons-append ' ')
  (∘-append (showsString (toList "denominator")) _ (showsString-split (toList "denominator"))
  (∘-append (':' ∷_) _ (cons-append ':') (∘-append (' ' ∷_) _ (cons-append ' ')
  (∘-append (showsℕ (suc (suc d))) ('}' ∷_) (showsℕ-split (suc (suc d))) (cons-append '}')))))))))))

mutual
  shows-split : ∀ j → AppendLike (showsJSON j)
  shows-split JNull         r = refl
  shows-split (JBool true)  r = refl
  shows-split (JBool false) r = refl
  shows-split (JNumber q)   r = showsRational-split q r
  shows-split (JString cs)  r = showsString-split cs r
  shows-split (JArray [])   r = refl
  shows-split (JArray (x ∷ xs)) =
    ∘-append ('[' ∷_) _ (cons-append '[')
      (∘-append (showsJSON x) _ (shows-split x) (∘-append (showsElements xs) (']' ∷_) (elements-split xs) (cons-append ']')))
  shows-split (JObject [])  r = refl
  shows-split (JObject ((k , v) ∷ fs)) =
    ∘-append ('{' ∷_) _ (cons-append '{')
      (∘-append (showsField k v) _ (field-split k v) (∘-append (showsFields fs) ('}' ∷_) (fields-split fs) (cons-append '}')))

  elements-split : ∀ xs → AppendLike (showsElements xs)
  elements-split []       r = refl
  elements-split (x ∷ xs) =
    ∘-append (',' ∷_) _ (cons-append ',') (∘-append (' ' ∷_) _ (cons-append ' ')
      (∘-append (showsJSON x) (showsElements xs) (shows-split x) (elements-split xs)))

  fields-split : ∀ fs → AppendLike (showsFields fs)
  fields-split []             r = refl
  fields-split ((k , v) ∷ fs) =
    ∘-append (',' ∷_) _ (cons-append ',') (∘-append (' ' ∷_) _ (cons-append ' ')
      (∘-append (showsField k v) (showsFields fs) (field-split k v) (fields-split fs)))

  field-split : ∀ k v → AppendLike (showsField k v)
  field-split k v =
    ∘-append (showsString (toList k)) _ (showsString-split (toList k))
      (∘-append (':' ∷_) _ (cons-append ':') (∘-append (' ' ∷_) (showsJSON v) (cons-append ' ') (shows-split v)))

-- ============================================================================
-- WHAT FOLLOWS A VALUE
-- ============================================================================

-- What follows a value the formatter writes: the end of the text, or a
-- comma, a closing bracket or a closing brace.
data ValueEnd : List Char → Set where
  end-text    : ValueEnd []
  end-comma   : ∀ {cs} → ValueEnd (',' ∷ cs)
  end-bracket : ∀ {cs} → ValueEnd (']' ∷ cs)
  end-brace   : ∀ {cs} → ValueEnd ('}' ∷ cs)

valueEnd-number : ∀ {r} → ValueEnd r → NumberEnd r
valueEnd-number end-text    = end-of-text
valueEnd-number end-comma   = end-at refl refl refl refl
valueEnd-number end-bracket = end-at refl refl refl refl
valueEnd-number end-brace   = end-at refl refl refl refl

-- No whitespace in front.
NoWs : List Char → Set
NoWs []      = ⊤
NoWs (c ∷ _) = isWhitespace c ≡ false

valueEnd-noWs : ∀ {r} → ValueEnd r → NoWs r
valueEnd-noWs end-text    = tt
valueEnd-noWs end-comma   = refl
valueEnd-noWs end-bracket = refl
valueEnd-noWs end-brace   = refl

-- ============================================================================
-- CHARACTERS
-- ============================================================================

digit-noWs : ∀ {c} → isDigitChar c ≡ true → isWhitespace c ≡ false
digit-noWs {c} dc = ¬-not (λ w → not-ws (any-≈ᵇ c whitespace w) dc)
  where
    not-ws : ∀ {c} → c ∈ whitespace → isDigitChar c ≡ true → ⊥
    not-ws (here refl)                         ()
    not-ws (there (here refl))                 ()
    not-ws (there (there (here refl)))         ()
    not-ws (there (there (there (here refl)))) ()
    not-ws (there (there (there (there ())))) _

-- Every value the formatter writes starts with a character that is not
-- whitespace.
shows-noWs : ∀ j r → NoWs (showsJSON j r)
shows-noWs JNull         r = refl
shows-noWs (JBool true)  r = refl
shows-noWs (JBool false) r = refl
shows-noWs (JNumber (mkℚ num zero _)) r with number-head num r
... | c , cs , eq , inj₁ refl = subst NoWs (sym eq) refl
... | c , cs , eq , inj₂ d    = subst NoWs (sym eq) (digit-noWs {c} d)
shows-noWs (JNumber (mkℚ num (suc _) _)) r = refl
shows-noWs (JString cs)  r = refl
shows-noWs (JArray [])   r = refl
shows-noWs (JArray (_ ∷ _)) r = refl
shows-noWs (JObject [])  r = refl
shows-noWs (JObject (_ ∷ _)) r = refl

-- ============================================================================
-- WHITESPACE AND STRUCTURAL CHARACTERS
-- ============================================================================

ws-reads-none : ∀ {r} → NoWs r → ReadsText ws [] [] r
ws-reads-none {[]}     _  = reading λ pos → refl
ws-reads-none {c ∷ cs} nw = reading (go nw)
  where
    go : isWhitespace c ≡ false → ∀ pos → proj₂ (ws pos (c ∷ cs)) ≡ just (mkResult [] pos (c ∷ cs))
    go nw pos with satisfy isWhitespace pos (c ∷ cs) | satisfy-nothing isWhitespace pos c cs nw
    ... | w , nothing | refl = refl

noWs-stops : ∀ {r} → NoWs r → ∀ pos → proj₂ (satisfy isWhitespace pos r) ≡ nothing
noWs-stops {[]}     _ pos = refl
noWs-stops {c ∷ cs} n pos = satisfy-nothing isWhitespace pos c cs n

ws-reads-space : ∀ {r} → NoWs r → ReadsText ws (' ' ∷ []) (' ' ∷ []) r
ws-reads-space {r} nw = many-reads {f = λ c → c} spaces
  where
    spaces : Reads (satisfy isWhitespace) (λ c r → c ∷ r) (λ c → c) r (' ' ∷ [])
    spaces = reads-more (λ pos → satisfy-just isWhitespace pos ' ' r refl) (λ _ → refl) (s≤s z≤n) (reads-none (noWs-stops nw))

char-reads : ∀ c {r} → ReadsText (char c) (c ∷ []) c r
char-reads c {r} = reading λ pos → satisfy-just (λ x → x ≈ᵇ c) pos c r (≈ᵇ-refl c)

-- The whitespace the formatter writes after a structural character: none,
-- or one space.
data Spacing : List Char → Set where
  no-space  : Spacing []
  one-space : Spacing (' ' ∷ [])

structural-reads : ∀ c {sp r} → isWhitespace c ≡ false → Spacing sp → NoWs r → ReadsText (structural c) (c ∷ sp) c r
structural-reads c c-nw no-space nw =
  before-reads {p = ws *> char c} {q = ws} {t₁ = c ∷ []} {t₂ = []}
    (then-reads {p = ws} {q = char c} {t₁ = []} {t₂ = c ∷ []} (ws-reads-none c-nw) (char-reads c)) (ws-reads-none nw)
structural-reads c c-nw one-space nw =
  before-reads {p = ws *> char c} {q = ws} {t₁ = c ∷ []} {t₂ = ' ' ∷ []}
    (then-reads {p = ws} {q = char c} {t₁ = []} {t₂ = c ∷ []} (ws-reads-none c-nw) (char-reads c)) (ws-reads-space nw)

-- ============================================================================
-- WHERE THE LITERALS FAIL
-- ============================================================================

private
  -- A literal fails on a text that does not start with its first character.
  literal-fails : ∀ {A : Set} (a : A) s {h hs} → toList s ≡ h ∷ hs → ∀ pos c cs → (c ≈ᵇ h) ≡ false →
    proj₂ ((a <$ string s) pos (c ∷ cs)) ≡ nothing
  literal-fails a s {h} {hs} eq pos c cs e =
    bind-nothing (string s) (λ _ → pure a) pos (c ∷ cs)
      (bind-nothing (parseCharsSeq (toList s)) (λ _ → pure s) pos (c ∷ cs)
        (subst (λ l → proj₂ (parseCharsSeq l pos (c ∷ cs)) ≡ nothing) (sym eq)
          (bind-nothing (char h) (λ x → parseCharsSeq hs >>= λ xs → pure (x ∷ xs)) pos (c ∷ cs)
            (satisfy-nothing (λ x → x ≈ᵇ h) pos c cs e))))

  -- No literal starts like a number.
  literals-fail : ∀ num r pos → proj₂ ((parseNull <|> parseBoolean) pos (showsℤ num r)) ≡ nothing
  literals-fail num r pos with number-head num r
  ... | c , cs , eq , head =
    subst (λ i → proj₂ ((parseNull <|> parseBoolean) pos i) ≡ nothing) (sym eq)
      (trans (alt-right parseNull parseBoolean pos (c ∷ cs) (literal-fails JNull "null" refl pos c cs (not-letter 'n' refl refl)))
             (trans (alt-right (JBool true <$ string "true") (JBool false <$ string "false") pos (c ∷ cs)
                       (literal-fails (JBool true) "true" refl pos c cs (not-letter 't' refl refl)))
                    (literal-fails (JBool false) "false" refl pos c cs (not-letter 'f' refl refl))))
    where
      not-letter : ∀ l → isDigitChar l ≡ false → ('-' ≈ᵇ l) ≡ false → (c ≈ᵇ l) ≡ false
      not-letter l dl dash = Sum.[ (λ e → subst (λ x → (x ≈ᵇ l) ≡ false) (sym e) dash) , (λ d → digit-≉ {c} l d dl) ]′ head

-- ============================================================================
-- LEAVES
-- ============================================================================

stringLit-reads : ∀ cs {r} → ReadsText parseStringChars (showsString cs []) cs r
stringLit-reads cs {r} = reads-from {p = parseStringChars} (showsString-split cs r) (λ pos → showsString-readback pos cs r)

number-reads : ∀ num {r} → ∣ num ∣ < heldMagnitude → ValueEnd r →
  ReadsText parseNumber (showsℤ num []) (JNumber (intValue num)) r
number-reads num {r} n< end = reads-from {p = parseNumber} (showsℤ-split num r) (λ pos → parseNumber-showsℤ pos num r n< (valueEnd-number end))

-- ============================================================================
-- LENGTHS
-- ============================================================================

length-mid : ∀ (pre mid post : List Char) → length mid ≤ length (pre ++ mid ++ post)
length-mid pre mid post =
  ≤-trans (m≤m+n (length mid) (length post))
    (≤-trans (≤-reflexive (sym (length-++ mid)))
      (≤-trans (m≤n+m (length (mid ++ post)) (length pre)) (≤-reflexive (sym (length-++ pre)))))

shows-nonempty : ∀ j → 0 < length (showsJSON j [])
shows-nonempty JNull                         = s≤s z≤n
shows-nonempty (JBool true)                  = s≤s z≤n
shows-nonempty (JBool false)                 = s≤s z≤n
shows-nonempty (JNumber (mkℚ num zero _))    with number-head num []
... | c , cs , eq , _ = subst (λ t → 0 < length t) (sym eq) (s≤s z≤n)
shows-nonempty (JNumber (mkℚ num (suc _) _)) = s≤s z≤n
shows-nonempty (JString cs)                  = s≤s z≤n
shows-nonempty (JArray [])                   = s≤s z≤n
shows-nonempty (JArray (_ ∷ _))              = s≤s z≤n
shows-nonempty (JObject [])                  = s≤s z≤n
shows-nonempty (JObject (_ ∷ _))             = s≤s z≤n

-- No whitespace in front of a value's text followed by anything.
shows-noWs++ : ∀ j ys → NoWs (showsJSON j [] ++ ys)
shows-noWs++ j ys = subst NoWs (shows-split j ys) (shows-noWs j ys)

length-suffix : ∀ (pre post : List Char) → length post ≤ length (pre ++ post)
length-suffix pre post = ≤-trans (m≤n+m (length post) (length pre)) (≤-reflexive (sym (length-++ pre)))

-- ============================================================================
-- ELEMENTS AND MEMBERS
-- ============================================================================

-- An array's element after the first, after its comma and space.
elementEnc : JSON → List Char → List Char
elementEnc x r = ',' ∷ ' ' ∷ showsJSON x r

-- An object's member after the first, after its comma and space.
fieldEnc : String × JSON → List Char → List Char
fieldEnc (k , v) r = ',' ∷ ' ' ∷ showsField k v r

readBackField : String × JSON → String × JSON
readBackField (k , v) = fromList (toList k) , readBack v

elements-encodeAll : ∀ xs r → showsElements xs r ≡ encodeAll elementEnc xs r
elements-encodeAll []       r = refl
elements-encodeAll (x ∷ xs) r = cong (λ z → ',' ∷ ' ' ∷ showsJSON x z) (elements-encodeAll xs r)

fields-encodeAll : ∀ fs r → showsFields fs r ≡ encodeAll fieldEnc fs r
fields-encodeAll []             r = refl
fields-encodeAll ((k , v) ∷ fs) r = cong (λ z → ',' ∷ ' ' ∷ showsField k v z) (fields-encodeAll fs r)

map-readBack : ∀ xs → map readBack xs ≡ readBackElements xs
map-readBack []       = refl
map-readBack (x ∷ xs) = cong (readBack x ∷_) (map-readBack xs)

map-readBackField : ∀ fs → map readBackField fs ≡ readBackFields fs
map-readBackField []             = refl
map-readBackField ((k , v) ∷ fs) = cong ((fromList (toList k) , readBack v) ∷_) (map-readBackField fs)

-- What follows an element or a member: a comma, or the closing bracket or brace.
elements-end : ∀ xs r → ValueEnd (encodeAll elementEnc xs (']' ∷ r))
elements-end []      r = end-bracket
elements-end (_ ∷ _) r = end-comma

fields-end : ∀ fs r → ValueEnd (encodeAll fieldEnc fs ('}' ∷ r))
fields-end []      r = end-brace
fields-end (_ ∷ _) r = end-comma

private
  -- A value written in an array or object: the closing character fails it.
  values-fail : ∀ b r pos → proj₂ (parseValues b pos (']' ∷ r)) ≡ nothing
  values-fail []      r pos = refl
  values-fail (_ ∷ b) r pos = refl

  members-fail : ∀ b r pos → proj₂ (parseMembers b pos ('}' ∷ r)) ≡ nothing
  members-fail b r pos = refl

  -- The array's text, taken apart as the parser reads it.
  array-text : ∀ x xs → ('[' ∷ (showsJSON x [] ++ encodeAll elementEnc xs [])) ++ (']' ∷ []) ≡ showsJSON (JArray (x ∷ xs)) []
  array-text x xs =
    cong ('[' ∷_)
      (trans (++-assoc (showsJSON x []) (encodeAll elementEnc xs []) (']' ∷ []))
             (trans (cong (showsJSON x [] ++_)
                          (trans (cong (_++ ']' ∷ []) (sym (elements-encodeAll xs []))) (sym (elements-split xs (']' ∷ [])))))
                    (sym (shows-split x (showsElements xs (']' ∷ []))))))

  object-text : ∀ k v fs →
    ('{' ∷ (showsField k v [] ++ encodeAll fieldEnc fs [])) ++ ('}' ∷ []) ≡ showsJSON (JObject ((k , v) ∷ fs)) []
  object-text k v fs =
    cong ('{' ∷_)
      (trans (++-assoc (showsField k v []) (encodeAll fieldEnc fs []) ('}' ∷ []))
             (trans (cong (showsField k v [] ++_)
                          (trans (cong (_++ '}' ∷ []) (sym (fields-encodeAll fs []))) (sym (fields-split fs ('}' ∷ [])))))
                    (sym (field-split k v (showsFields fs ('}' ∷ []))))))

  field-text : ∀ k v → (showsString (toList k) [] ++ (':' ∷ ' ' ∷ [])) ++ showsJSON v [] ≡ showsField k v []
  field-text k v =
    trans (++-assoc (showsString (toList k) []) (':' ∷ ' ' ∷ []) (showsJSON v []))
          (sym (showsString-split (toList k) (':' ∷ ' ' ∷ showsJSON v [])))

  -- The parser's alternatives before an array, and before an object.
  beforeArray : Parser JSON
  beforeArray = ((parseNull <|> parseBoolean) <|> parseNumber) <|> parseString

  beforeObject : List Char → Parser JSON
  beforeObject b = beforeArray <|> parseArray b

-- The bound an integer's denominator meets.
0<held : 0 < heldMagnitude
0<held = <ᵇ⇒< 0 heldMagnitude tt

1<held : 1 < heldMagnitude
1<held = <ᵇ⇒< 1 heldMagnitude tt

-- The two members a rational with a denominator above 1 is written as.
fraction : ℤ → ℕ → List (String × JSON)
fraction num d = ("numerator" , JNumber (intValue num)) ∷ ("denominator" , JNumber (intValue (+ suc (suc d)))) ∷ []

-- ============================================================================
-- VALUES
-- ============================================================================

mutual
  value-reads : ∀ b j → NumbersSatisfy ReadExactly j → length (showsJSON j []) ≤ length b → ∀ {r} → ValueEnd r →
    ReadsText (parseValue b) (showsJSON j []) (readBack j) r
  value-reads [] j _ len _ = contradiction (≤-trans (shows-nonempty j) len) (λ ())
  value-reads (_ ∷ b) JNull         _ _ _ = reading λ pos → refl
  value-reads (_ ∷ b) (JBool true)  _ _ _ = reading λ pos → refl
  value-reads (_ ∷ b) (JBool false) _ _ _ = reading λ pos → refl
  value-reads (_ ∷ b) (JNumber (mkℚ num zero _)) (n< , _) _ {r} end =
    alt-left-reads {q = parseObject b} (alt-left-reads {q = parseArray b} (alt-left-reads {q = parseString}
      (alt-right-reads {p = parseNull <|> parseBoolean}
        (λ pos → subst (λ i → proj₂ ((parseNull <|> parseBoolean) pos i) ≡ nothing) (showsℤ-split num r) (literals-fail num r pos))
        (number-reads num n< end))))
  value-reads (_ ∷ b) (JNumber (mkℚ (+ zero) (suc d) _)) (_ , d<) len end =
    alt-right-reads {p = beforeObject b} (λ pos → refl)
      (object-reads b (fraction (+ zero) d) ((0<held , 1<held) , (d< , 1<held) , tt) len end)
  value-reads (_ ∷ b) (JNumber (mkℚ (+ suc n) (suc d) _)) (n< , d<) len end =
    alt-right-reads {p = beforeObject b} (λ pos → refl)
      (object-reads b (fraction (+ suc n) d) ((n< , 1<held) , (d< , 1<held) , tt) len end)
  value-reads (_ ∷ b) (JNumber (mkℚ -[1+ n ] (suc d) _)) (n< , d<) len end =
    alt-right-reads {p = beforeObject b} (λ pos → refl)
      (object-reads b (fraction -[1+ n ] d) ((n< , 1<held) , (d< , 1<held) , tt) len end)
  value-reads (_ ∷ b) (JString cs) _ _ end =
    alt-left-reads {q = parseObject b} (alt-left-reads {q = parseArray b}
      (alt-right-reads {p = (parseNull <|> parseBoolean) <|> parseNumber} (λ pos → refl) (map-reads {g = JString} (stringLit-reads cs))))
  value-reads (_ ∷ b) (JArray []) fits len end =
    alt-left-reads {q = parseObject b} (alt-right-reads {p = beforeArray} (λ pos → refl) (array-reads b [] fits len end))
  value-reads (_ ∷ b) (JArray (x ∷ xs)) fits len end =
    alt-left-reads {q = parseObject b} (alt-right-reads {p = beforeArray} (λ pos → refl) (array-reads b (x ∷ xs) fits len end))
  value-reads (_ ∷ b) (JObject []) fits len end =
    alt-right-reads {p = beforeObject b} (λ pos → refl) (object-reads b [] fits len end)
  value-reads (_ ∷ b) (JObject (f ∷ fs)) fits len end =
    alt-right-reads {p = beforeObject b} (λ pos → refl) (object-reads b (f ∷ fs) fits len end)

  array-reads : ∀ b xs → ListNumbersSatisfy ReadExactly xs → length (showsJSON (JArray xs) []) ≤ suc (length b) → ∀ {r} → ValueEnd r →
    ReadsText (parseArray b) (showsJSON (JArray xs) []) (JArray (readBackElements xs)) r
  array-reads b [] _ _ {r} end =
    before-reads {p = structural '[' *> (JArray <$> (parseValues b <|> pure []))} {q = structural ']'}
                 {t₁ = '[' ∷ []} {t₂ = ']' ∷ []}
      (then-reads {p = structural '['} {q = JArray <$> (parseValues b <|> pure [])} {t₁ = '[' ∷ []} {t₂ = []}
        (structural-reads '[' refl no-space refl)
        (map-reads {g = JArray} (alt-right-reads {p = parseValues b} (λ pos → values-fail b r pos) (pure-reads []))))
      (structural-reads ']' refl no-space (valueEnd-noWs end))
  array-reads b (x ∷ xs) (fx , fxs) len {r} end =
    reads-text (array-text x xs) (reads-value (cong (λ vs → JArray (readBack x ∷ vs)) (map-readBack xs))
      (before-reads {p = structural '[' *> (JArray <$> (parseValues b <|> pure []))} {q = structural ']'}
                    {t₁ = '[' ∷ (showsJSON x [] ++ E)} {t₂ = ']' ∷ []}
        (then-reads {p = structural '['} {q = JArray <$> (parseValues b <|> pure [])} {t₁ = '[' ∷ []} {t₂ = showsJSON x [] ++ E}
          (structural-reads '[' refl no-space (subst NoWs (sym (++-assoc (showsJSON x []) E (']' ∷ r))) (shows-noWs++ x (E ++ ']' ∷ r))))
          (map-reads {g = JArray} (alt-left-reads {q = pure []}
            (ap-reads {pf = _∷_ <$> parseValue b} {px = many (structural ',' *> parseValue b)} {t₁ = showsJSON x []} {t₂ = E}
              (map-reads {g = _∷_} (value-reads b x fx len-x (elements-tail xs r)))
              (many-reads (elements-reads b xs fxs len-xs))))))
        (structural-reads ']' refl no-space (valueEnd-noWs end))))
    where
      E = encodeAll elementEnc xs []
      inner : length ((showsJSON x [] ++ E) ++ (']' ∷ [])) ≤ length b
      inner = ≤-pred (subst (λ t → length t ≤ suc (length b)) (sym (array-text x xs)) len)
      inner′ : length (showsJSON x [] ++ E ++ (']' ∷ [])) ≤ length b
      inner′ = subst (_≤ length b) (cong length (++-assoc (showsJSON x []) E (']' ∷ []))) inner
      len-x : length (showsJSON x []) ≤ length b
      len-x = ≤-trans (length-mid [] (showsJSON x []) (E ++ (']' ∷ []))) inner′
      len-xs : length E ≤ length b
      len-xs = ≤-trans (length-mid (showsJSON x []) E (']' ∷ [])) inner′

  -- What follows the first element: the others, then the closing bracket.
  elements-tail : ∀ xs r → ValueEnd (encodeAll elementEnc xs [] ++ ']' ∷ r)
  elements-tail []      r = end-bracket
  elements-tail (_ ∷ _) r = end-comma

  elements-reads : ∀ b xs → ListNumbersSatisfy ReadExactly xs → length (encodeAll elementEnc xs []) ≤ length b → ∀ {r} →
    Reads (structural ',' *> parseValue b) elementEnc readBack (']' ∷ r) xs
  elements-reads b [] _ _ = reads-none (λ pos → refl)
  elements-reads b (y ∷ ys) (fy , fys) len {r} =
    reads-more element (λ rest → cong (λ z → ',' ∷ ' ' ∷ z) (shows-split y rest)) (s≤s z≤n) (elements-reads b ys fys len-ys)
    where
      R = encodeAll elementEnc ys (']' ∷ r)
      E′ = encodeAll elementEnc ys []
      text : length (',' ∷ ' ' ∷ (showsJSON y [] ++ E′)) ≤ length b
      text = subst (λ t → length t ≤ length b) (cong (λ z → ',' ∷ ' ' ∷ z) (shows-split y E′)) len
      len-y : length (showsJSON y []) ≤ length b
      len-y = ≤-trans (length-mid (',' ∷ ' ' ∷ []) (showsJSON y []) E′) text
      len-ys : length E′ ≤ length b
      len-ys = ≤-trans (length-suffix (',' ∷ ' ' ∷ showsJSON y []) E′) text
      element : ∀ pos → proj₂ ((structural ',' *> parseValue b) pos (elementEnc y R))
                         ≡ just (mkResult (readBack y) (advancePositions pos (elementEnc y [])) R)
      element pos =
        subst (λ i → proj₂ ((structural ',' *> parseValue b) pos i) ≡ just (mkResult (readBack y) (advancePositions pos (elementEnc y [])) R))
              (cong (λ z → ',' ∷ ' ' ∷ z) (sym (shows-split y R)))
              (then-reads {p = structural ','} {q = parseValue b} {t₁ = ',' ∷ ' ' ∷ []} {t₂ = showsJSON y []}
                 (structural-reads ',' refl one-space (shows-noWs++ y R)) (value-reads b y fy len-y (elements-end ys r)) .readsAt pos)

  object-reads : ∀ b fs → FieldsNumbersSatisfy ReadExactly fs → length (showsJSON (JObject fs) []) ≤ suc (length b) → ∀ {r} →
    ValueEnd r → ReadsText (parseObject b) (showsJSON (JObject fs) []) (JObject (readBackFields fs)) r
  object-reads b [] _ _ {r} end =
    before-reads {p = structural '{' *> (JObject <$> (parseMembers b <|> pure []))} {q = structural '}'}
                 {t₁ = '{' ∷ []} {t₂ = '}' ∷ []}
      (then-reads {p = structural '{'} {q = JObject <$> (parseMembers b <|> pure [])} {t₁ = '{' ∷ []} {t₂ = []}
        (structural-reads '{' refl no-space refl)
        (map-reads {g = JObject} (alt-right-reads {p = parseMembers b} (λ pos → members-fail b r pos) (pure-reads []))))
      (structural-reads '}' refl no-space (valueEnd-noWs end))
  object-reads b ((k , v) ∷ fs) (fv , ffs) len {r} end =
    reads-text (object-text k v fs) (reads-value (cong (λ ms → JObject ((fromList (toList k) , readBack v) ∷ ms)) (map-readBackField fs))
      (before-reads {p = structural '{' *> (JObject <$> (parseMembers b <|> pure []))} {q = structural '}'}
                    {t₁ = '{' ∷ (showsField k v [] ++ F)} {t₂ = '}' ∷ []}
        (then-reads {p = structural '{'} {q = JObject <$> (parseMembers b <|> pure [])} {t₁ = '{' ∷ []} {t₂ = showsField k v [] ++ F}
          (structural-reads '{' refl no-space refl)
          (map-reads {g = JObject} (alt-left-reads {q = pure []}
            (ap-reads {pf = _∷_ <$> parseMember b} {px = many (structural ',' *> parseMember b)} {t₁ = showsField k v []} {t₂ = F}
              (map-reads {g = _∷_} (member-reads b k v fv len-v (fields-tail fs r)))
              (many-reads (fields-reads b fs ffs len-fs))))))
        (structural-reads '}' refl no-space (valueEnd-noWs end))))
    where
      F = encodeAll fieldEnc fs []
      inner : length ((showsField k v [] ++ F) ++ ('}' ∷ [])) ≤ length b
      inner = ≤-pred (subst (λ t → length t ≤ suc (length b)) (sym (object-text k v fs)) len)
      inner′ : length (showsField k v [] ++ F ++ ('}' ∷ [])) ≤ length b
      inner′ = subst (_≤ length b) (cong length (++-assoc (showsField k v []) F ('}' ∷ []))) inner
      len-field : length (showsField k v []) ≤ length b
      len-field = ≤-trans (length-mid [] (showsField k v []) (F ++ ('}' ∷ []))) inner′
      len-v : length (showsJSON v []) ≤ length b
      len-v = ≤-trans (≤-trans (length-suffix (showsString (toList k) [] ++ (':' ∷ ' ' ∷ [])) (showsJSON v []))
                                (≤-reflexive (cong length (field-text k v)))) len-field
      len-fs : length F ≤ length b
      len-fs = ≤-trans (length-mid (showsField k v []) F ('}' ∷ [])) inner′

  fields-tail : ∀ fs r → ValueEnd (encodeAll fieldEnc fs [] ++ '}' ∷ r)
  fields-tail []      r = end-brace
  fields-tail (_ ∷ _) r = end-comma

  member-reads : ∀ b k v → NumbersSatisfy ReadExactly v → length (showsJSON v []) ≤ length b → ∀ {r} → ValueEnd r →
    ReadsText (parseMember b) (showsField k v []) (fromList (toList k) , readBack v) r
  member-reads b k v fv len {r} end =
    reads-text (field-text k v)
      (ap-reads {pf = memberOf <$> (parseStringChars <* structural ':')} {px = parseValue b}
                {t₁ = showsString (toList k) [] ++ (':' ∷ ' ' ∷ [])} {t₂ = showsJSON v []}
        (map-reads {g = memberOf}
          (before-reads {p = parseStringChars} {q = structural ':'} {t₁ = showsString (toList k) []} {t₂ = ':' ∷ ' ' ∷ []}
            (stringLit-reads (toList k)) (structural-reads ':' refl one-space (shows-noWs++ v r))))
        (value-reads b v fv len end))

  fields-reads : ∀ b fs → FieldsNumbersSatisfy ReadExactly fs → length (encodeAll fieldEnc fs []) ≤ length b → ∀ {r} →
    Reads (structural ',' *> parseMember b) fieldEnc readBackField ('}' ∷ r) fs
  fields-reads b [] _ _ = reads-none (λ pos → refl)
  fields-reads b ((k , v) ∷ fs) (fv , ffs) len {r} =
    reads-more member′ (λ rest → cong (λ z → ',' ∷ ' ' ∷ z) (field-split k v rest)) (s≤s z≤n) (fields-reads b fs ffs len-fs)
    where
      R = encodeAll fieldEnc fs ('}' ∷ r)
      F′ = encodeAll fieldEnc fs []
      text : length (',' ∷ ' ' ∷ (showsField k v [] ++ F′)) ≤ length b
      text = subst (λ t → length t ≤ length b) (cong (λ z → ',' ∷ ' ' ∷ z) (field-split k v F′)) len
      len-field : length (showsField k v []) ≤ length b
      len-field = ≤-trans (length-mid (',' ∷ ' ' ∷ []) (showsField k v []) F′) text
      len-v : length (showsJSON v []) ≤ length b
      len-v = ≤-trans (≤-trans (length-suffix (showsString (toList k) [] ++ (':' ∷ ' ' ∷ [])) (showsJSON v []))
                                (≤-reflexive (cong length (field-text k v)))) len-field
      len-fs : length F′ ≤ length b
      len-fs = ≤-trans (length-suffix (',' ∷ ' ' ∷ showsField k v []) F′) text
      member′ : ∀ pos → proj₂ ((structural ',' *> parseMember b) pos (fieldEnc (k , v) R))
                         ≡ just (mkResult (readBackField (k , v)) (advancePositions pos (fieldEnc (k , v) [])) R)
      member′ pos =
        subst (λ i → proj₂ ((structural ',' *> parseMember b) pos i)
                       ≡ just (mkResult (readBackField (k , v)) (advancePositions pos (fieldEnc (k , v) [])) R))
              (cong (λ z → ',' ∷ ' ' ∷ z) (sym (field-split k v R)))
              (then-reads {p = structural ','} {q = parseMember b} {t₁ = ',' ∷ ' ' ∷ []} {t₂ = showsField k v []}
                 (structural-reads ',' refl one-space refl) (member-reads b k v fv len-v (fields-end fs r)) .readsAt pos)


-- ============================================================================
-- THE ROUND TRIP
-- ============================================================================

eof-reads : ReadsText eof [] tt []
eof-reads = reading λ pos → refl

-- The parser reads back whole what the formatter writes, for every value
-- whose numbers have a numerator magnitude and a denominator below 2^64.
parseJSON-formatJSONChars : ∀ pos j → NumbersSatisfy ReadExactly j →
  proj₂ (parseJSON pos (formatJSONChars j))
    ≡ just (mkResult (wire (rekey j)) (advancePositions pos (formatJSONChars j)) [])
parseJSON-formatJSONChars pos j fits =
  trans (subst (λ i → proj₂ (text pos i) ≡ just (mkResult (readBack j) (advancePositions pos T) []))
               (++-identityʳ T) (readsAt whole pos))
        (cong (λ v → just (mkResult v (advancePositions pos T) [])) (readBack-wire-rekey j))
  where
    T = formatJSONChars j
    text : Parser JSON
    text = ws *> parseValue T <* ws <* eof
    whole : ReadsText text T (readBack j) []
    whole =
      reads-text (trans (++-identityʳ (T ++ [])) (++-identityʳ T))
        (before-reads {p = ws *> parseValue T <* ws} {q = eof} {t₁ = T ++ []} {t₂ = []}
          (before-reads {p = ws *> parseValue T} {q = ws} {t₁ = T} {t₂ = []}
            (then-reads {p = ws} {q = parseValue T} {t₁ = []} {t₂ = T}
              (ws-reads-none (shows-noWs++ j [])) (value-reads T j fits ≤-refl end-text))
            (ws-reads-none tt))
          eof-reads)
