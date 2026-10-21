-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- What a parser's success says about its input.
--
-- `Sound p R` holds when every success of `p` splits its input into the
-- characters it consumed, followed by what it left, with `R` relating the
-- consumed characters to the value it returned.  Each combinator builds the
-- relation of the parser it makes from the relations of its parts, so the
-- soundness of a parser follows its definition.
module Aletheia.Parser.Properties.Sound where

open import Data.Bool using (Bool; true; false; if_then_else_)
import Data.Bool
open import Data.Char using (Char; _≈ᵇ_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₂)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Aletheia.Parser.Combinators using (Parser; ParseResult; mkResult; value; position; remaining; pure; fail; _>>=_; _<$>_; _<*>_; _<|>_; _*>_; _<*_; satisfy; char; many; manyHelper; eof; parseCharsSeq; string; optional)
open import Aletheia.Parser.Position using (samePosᵇ)
open import Aletheia.Parser.Properties.Chars using (≈ᵇ⇒≡)

-- Every success of `p` consumed characters `R` relates to its value.
record Sound {A : Set} (p : Parser A) (R : List Char → A → Set) : Set where
  constructor sound
  field
    split : ∀ pos input r → proj₂ (p pos input) ≡ just r →
            Σ[ cs ∈ List Char ] (input ≡ cs ++ remaining r × R cs (value r))

open Sound public

-- The relation of a sequence: the first part's characters, then the second's.
_⨾_ : ∀ {A B : Set} → (List Char → A → Set) → (A → List Char → B → Set) → List Char → B → Set
_⨾_ {A} R S cs b = Σ[ xs ∈ List Char ] Σ[ ys ∈ List Char ] Σ[ a ∈ A ] (cs ≡ xs ++ ys × R xs a × S a ys b)

infixr 5 _⨾_

-- An input split after `xs`, whose rest is split again after `ys`.
resplit : ∀ {input rest′ : List Char} (xs ys rest : List Char) →
  input ≡ xs ++ rest′ → rest′ ≡ ys ++ rest → input ≡ (xs ++ ys) ++ rest
resplit xs ys rest i₁ i₂ = trans i₁ (trans (cong (xs ++_) i₂) (sym (++-assoc xs ys rest)))

-- A relation weakened to one it implies.
weaken : ∀ {A : Set} {p : Parser A} {R S : List Char → A → Set} →
  (∀ {cs a} → R cs a → S cs a) → Sound p R → Sound p S
weaken f sp = sound λ pos input r eq → let (cs , i , rc) = split sp pos input r eq in cs , i , f rc

pure-sound : ∀ {A : Set} (a : A) → Sound (pure a) (λ cs x → cs ≡ [] × x ≡ a)
pure-sound a = sound go
  where
    go : ∀ pos input r → proj₂ (pure a pos input) ≡ just r → _
    go pos input .(mkResult a pos input) refl = [] , refl , refl , refl

fail-sound : ∀ {A : Set} → Sound {A} fail (λ _ _ → ⊥)
fail-sound = sound λ { pos input r () }

satisfy-sound : ∀ (P : Char → Bool) → Sound (satisfy P) (λ cs c → cs ≡ c ∷ [] × P c ≡ true)
satisfy-sound P = sound go
  where
    go : ∀ pos input r → proj₂ (satisfy P pos input) ≡ just r →
         Σ[ cs ∈ List Char ] (input ≡ cs ++ remaining r × (cs ≡ value r ∷ [] × P (value r) ≡ true))
    go pos [] r ()
    go pos (c ∷ cs) r eq with P c in pc
    go pos (c ∷ cs) .(mkResult c _ cs) refl | true = c ∷ [] , refl , refl , pc

char-sound : ∀ (t : Char) → Sound (char t) (λ cs c → cs ≡ t ∷ [] × c ≡ t)
char-sound t = weaken conv (satisfy-sound (λ c → c ≈ᵇ t))
  where
    conv : ∀ {cs c} → cs ≡ c ∷ [] × (c ≈ᵇ t) ≡ true → cs ≡ t ∷ [] × c ≡ t
    conv {c = c} (refl , ct) with ≈ᵇ⇒≡ {c} {t} ct
    ... | refl = refl , refl

bind-sound : ∀ {A B : Set} {p : Parser A} {f : A → Parser B} {R : List Char → A → Set}
  {S : A → List Char → B → Set} → Sound p R → (∀ a → Sound (f a) (S a)) → Sound (p >>= f) (R ⨾ S)
bind-sound {p = p} {f} {R} {S} sp sf = sound go
  where
    go : ∀ pos input r → proj₂ ((p >>= f) pos input) ≡ just r →
         Σ[ cs ∈ List Char ] (input ≡ cs ++ remaining r × (R ⨾ S) cs (value r))
    go pos input r eq with p pos input in e₁
    ... | w , just r₁ with f (value r₁) (position r₁) (remaining r₁) in e₂
    ...   | w′ , just r₂ with eq
    ...     | refl with split sp pos input r₁ (cong proj₂ e₁)
                      | split (sf (value r₁)) (position r₁) (remaining r₁) r₂ (cong proj₂ e₂)
    ...       | xs , i₁ , rx | ys , i₂ , sy =
      xs ++ ys , resplit xs ys (remaining r₂) i₁ i₂ , xs , ys , value r₁ , refl , rx , sy

map-sound : ∀ {A B : Set} {g : A → B} {p : Parser A} {R : List Char → A → Set} →
  Sound p R → Sound (g <$> p) (λ cs b → Σ[ a ∈ A ] (R cs a × b ≡ g a))
map-sound {A} {g = g} {p} {R} sp = sound go
  where
    go : ∀ pos input r → proj₂ ((g <$> p) pos input) ≡ just r →
         Σ[ cs ∈ List Char ] (input ≡ cs ++ remaining r × Σ[ a ∈ A ] (R cs a × value r ≡ g a))
    go pos input r eq with p pos input in e
    ... | w , just r₁ with eq
    ...   | refl with split sp pos input r₁ (cong proj₂ e)
    ...     | cs , i , rc = cs , i , value r₁ , rc , refl

ap-sound : ∀ {A B : Set} {pf : Parser (A → B)} {px : Parser A}
  {R : List Char → (A → B) → Set} {S : List Char → A → Set} →
  Sound pf R → Sound px S →
  Sound (pf <*> px) (λ cs b → Σ[ xs ∈ List Char ] Σ[ ys ∈ List Char ] Σ[ g ∈ (A → B) ] Σ[ a ∈ A ]
                               (cs ≡ xs ++ ys × R xs g × S ys a × b ≡ g a))
ap-sound {A} {B} {pf = pf} {px} {R} {S} sf sx = sound go
  where
    go : ∀ pos input r → proj₂ ((pf <*> px) pos input) ≡ just r →
         Σ[ cs ∈ List Char ] (input ≡ cs ++ remaining r ×
           Σ[ xs ∈ List Char ] Σ[ ys ∈ List Char ] Σ[ g ∈ (A → B) ] Σ[ a ∈ A ]
             (cs ≡ xs ++ ys × R xs g × S ys a × value r ≡ g a))
    go pos input r eq with pf pos input in e₁
    ... | w , just r₁ with (value r₁ <$> px) (position r₁) (remaining r₁) in e₂
    ...   | w′ , just r₂ with eq
    ...     | refl with split sf pos input r₁ (cong proj₂ e₁)
                      | split (map-sound {g = value r₁} {px} sx) (position r₁) (remaining r₁) r₂ (cong proj₂ e₂)
    ...       | xs , i₁ , rg | ys , i₂ , a , sa , b≡ =
      xs ++ ys , resplit xs ys (remaining r₂) i₁ i₂ , xs , ys , value r₁ , a , refl , rg , sa , b≡

alt-sound : ∀ {A : Set} {p q : Parser A} {R S : List Char → A → Set} →
  Sound p R → Sound q S → Sound (p <|> q) (λ cs a → R cs a ⊎ S cs a)
alt-sound {A} {p = p} {q} {R} {S} sp sq = sound go
  where
    go : ∀ pos input r → proj₂ ((p <|> q) pos input) ≡ just r →
         Σ[ cs ∈ List Char ] (input ≡ cs ++ remaining r × (R cs (value r) ⊎ S cs (value r)))
    go pos input r eq with p pos input in e₁
    ... | w , just r₁ with eq
    ...   | refl with split sp pos input r₁ (cong proj₂ e₁)
    ...     | cs , i , rc = cs , i , inj₁ rc
    go pos input r eq | w , nothing with q pos input in e₂
    ...   | w′ , just r₂ with eq
    ...     | refl with split sq pos input r₂ (cong proj₂ e₂)
    ...       | cs , i , sc = cs , i , inj₂ sc

-- The relation of `p *> q`: `p`'s characters, then `q`'s, with `q`'s value.
then-sound : ∀ {A B : Set} {p : Parser A} {q : Parser B} {R : List Char → A → Set}
  {S : List Char → B → Set} → Sound p R → Sound q S → Sound (p *> q) (R ⨾ λ _ → S)
then-sound sp sq = bind-sound sp (λ _ → sq)

-- The relation of `p <* q`: `p`'s characters, then `q`'s, with `p`'s value.
before-sound : ∀ {A B : Set} {p : Parser A} {q : Parser B} {R : List Char → A → Set}
  {S : List Char → B → Set} → Sound p R → Sound q S →
  Sound (p <* q) (λ cs a → Σ[ xs ∈ List Char ] Σ[ ys ∈ List Char ] Σ[ b ∈ B ] (cs ≡ xs ++ ys × R xs a × S ys b))
before-sound {A} {B} {R = R} {S} sp sq = weaken conv (bind-sound sp (λ x → bind-sound sq (λ _ → pure-sound x)))
  where
    conv : ∀ {cs a} → (R ⨾ (λ x → S ⨾ (λ _ cs v → cs ≡ [] × v ≡ x))) cs a →
      Σ[ xs ∈ List Char ] Σ[ ys ∈ List Char ] Σ[ b ∈ B ] (cs ≡ xs ++ ys × R xs a × S ys b)
    conv (xs , ys , a′ , refl , rx , ys₁ , ys₂ , b , refl , sy , refl , refl) =
      xs , ys₁ , b , cong (xs ++_) (++-identityʳ ys₁) , rx , sy

-- A list of characters parsed one by one, each to itself.
parseCharsSeq-sound : ∀ cs → Sound (parseCharsSeq cs) (λ xs v → xs ≡ cs × v ≡ cs)
parseCharsSeq-sound [] = weaken (λ { (refl , refl) → refl , refl }) (pure-sound [])
parseCharsSeq-sound (c ∷ cs) =
  weaken conv (bind-sound (char-sound c) (λ x → bind-sound (parseCharsSeq-sound cs) (λ xs → pure-sound (x ∷ xs))))
  where
    conv : ∀ {zs v} →
      ((λ ys x → ys ≡ c ∷ [] × x ≡ c) ⨾ (λ x → (λ ys xs → ys ≡ cs × xs ≡ cs) ⨾ (λ xs ys w → ys ≡ [] × w ≡ x ∷ xs))) zs v →
      zs ≡ c ∷ cs × v ≡ c ∷ cs
    conv (.(c ∷ []) , ys , .c , refl , (refl , refl) , .cs , .[] , .cs , refl , (refl , refl) , (refl , refl)) =
      cong (c ∷_) (++-identityʳ cs) , refl

string-sound : ∀ s → Sound (string s) (λ xs _ → xs ≡ toList s)
string-sound s = weaken conv (bind-sound (parseCharsSeq-sound (toList s)) (λ _ → pure-sound s))
  where
    conv : ∀ {zs v} →
      ((λ ys x → ys ≡ toList s × x ≡ toList s) ⨾ (λ _ ys w → ys ≡ [] × w ≡ s)) zs v → zs ≡ toList s
    conv (xs , .[] , _ , refl , (refl , _) , (refl , _)) = ++-identityʳ _

-- `optional p`: nothing consumed, or what `p` consumed.
optional-sound : ∀ {A : Set} {p : Parser A} {R : List Char → A → Set} → Sound p R →
  Sound (optional p) (λ cs m → (cs ≡ [] × m ≡ nothing) ⊎ Σ[ a ∈ A ] (R cs a × m ≡ just a))
optional-sound {A} {R = R} sp = weaken conv (alt-sound (map-sound {g = just} sp) (pure-sound nothing))
  where
    conv : ∀ {cs m} → Σ[ a ∈ A ] (R cs a × m ≡ just a) ⊎ (cs ≡ [] × m ≡ nothing) →
      (cs ≡ [] × m ≡ nothing) ⊎ Σ[ a ∈ A ] (R cs a × m ≡ just a)
    conv (inj₁ (a , ra , refl)) = inj₂ (a , ra , refl)
    conv (inj₂ (refl , refl))   = inj₁ (refl , refl)

-- The relation of a repetition: the parts' characters, one after another,
-- each related to its value.
data Star {A : Set} (R : List Char → A → Set) : List Char → List A → Set where
  star-none : Star R [] []
  star-more : ∀ {xs ys a as} → R xs a → Star R ys as → Star R (xs ++ ys) (a ∷ as)

manyHelper-sound : ∀ {A : Set} {p : Parser A} {R : List Char → A → Set} → Sound p R →
  ∀ bound → Sound (λ pos input → manyHelper p pos input bound) (Star R)
manyHelper-sound {A} {p} {R} sp bound = sound (go bound)
  where
    go : ∀ bound pos input r → proj₂ (manyHelper p pos input bound) ≡ just r →
         Σ[ cs ∈ List Char ] (input ≡ cs ++ remaining r × Star R cs (value r))
    go [] pos input .(mkResult [] pos input) refl = [] , refl , star-none
    go (_ ∷ bound) pos input r eq with p pos input in e₁
    ... | w , nothing with eq
    ...   | refl = [] , refl , star-none
    go (_ ∷ bound) pos input r eq | w , just r₁ with samePosᵇ (position r₁) pos
    ... | true with eq
    ...   | refl = [] , refl , star-none
    go (_ ∷ bound) pos input r eq | w , just r₁ | false with manyHelper p (position r₁) (remaining r₁) bound in e₂
    ... | w′ , nothing with eq
    ...   | refl with split sp pos input r₁ (cong proj₂ e₁)
    ...     | xs , i₁ , rx = xs , i₁ , subst (λ z → Star R z (value r₁ ∷ [])) (++-identityʳ xs) (star-more rx star-none)
    go (_ ∷ bound) pos input r eq | w , just r₁ | false | w′ , just r₂ with eq
    ...   | refl with split sp pos input r₁ (cong proj₂ e₁) | go bound (position r₁) (remaining r₁) r₂ (cong proj₂ e₂)
    ...     | xs , i₁ , rx | ys , i₂ , sy = xs ++ ys , resplit xs ys (remaining r₂) i₁ i₂ , star-more rx sy

many-sound : ∀ {A : Set} {p : Parser A} {R : List Char → A → Set} → Sound p R → Sound (many p) (Star R)
many-sound sp = sound λ pos input → split (manyHelper-sound sp input) pos input

-- A repetition of single characters, each passing `P`.
star-satisfy : ∀ {P : Char → Bool} {cs vs} → Star (λ xs c → xs ≡ c ∷ [] × P c ≡ true) cs vs →
  cs ≡ vs × All (λ c → P c ≡ true) cs
star-satisfy star-none = refl , []
star-satisfy (star-more (refl , pc) s) with star-satisfy s
... | refl , all = refl , pc ∷ all

-- `eof` succeeds only on the empty input, leaving it empty.
eof-sound : ∀ pos input r → proj₂ (eof pos input) ≡ just r → input ≡ [] × remaining r ≡ []
eof-sound pos [] .(mkResult tt pos []) refl = refl , refl
eof-sound pos (_ ∷ _) r ()

-- ============================================================================
-- LANGUAGES: soundness that ignores the value
-- ============================================================================

-- `p` consumes only lists in `L`.
Accepts : ∀ {A : Set} → Parser A → (List Char → Set) → Set
Accepts p L = Sound p (λ cs _ → L cs)

-- Two languages one after the other.
_·_ : (List Char → Set) → (List Char → Set) → List Char → Set
(L₁ · L₂) cs = Σ[ xs ∈ List Char ] Σ[ ys ∈ List Char ] (cs ≡ xs ++ ys × L₁ xs × L₂ ys)

infixl 6 _·_

accepts-map : ∀ {A B : Set} {g : A → B} {p : Parser A} {L} → Accepts p L → Accepts (g <$> p) L
accepts-map {g = g} sp = weaken (λ (_ , l , _) → l) (map-sound {g = g} sp)

accepts-ap : ∀ {A B : Set} {pf : Parser (A → B)} {px : Parser A} {L₁ L₂} →
  Accepts pf L₁ → Accepts px L₂ → Accepts (pf <*> px) (L₁ · L₂)
accepts-ap sf sx = weaken (λ (xs , ys , _ , _ , e , l₁ , l₂ , _) → xs , ys , e , l₁ , l₂) (ap-sound sf sx)

accepts-alt : ∀ {A : Set} {p q : Parser A} {L₁ L₂} →
  Accepts p L₁ → Accepts q L₂ → Accepts (p <|> q) (λ cs → L₁ cs ⊎ L₂ cs)
accepts-alt sp sq = alt-sound sp sq

accepts-then : ∀ {A B : Set} {p : Parser A} {q : Parser B} {L₁ L₂} →
  Accepts p L₁ → Accepts q L₂ → Accepts (p *> q) (L₁ · L₂)
accepts-then sp sq = weaken (λ (xs , ys , _ , e , l₁ , l₂) → xs , ys , e , l₁ , l₂) (then-sound sp sq)

accepts-before : ∀ {A B : Set} {p : Parser A} {q : Parser B} {L₁ L₂} →
  Accepts p L₁ → Accepts q L₂ → Accepts (p <* q) (L₁ · L₂)
accepts-before sp sq = weaken (λ (xs , ys , _ , e , l₁ , l₂) → xs , ys , e , l₁ , l₂) (before-sound sp sq)

accepts-bind : ∀ {A B : Set} {p : Parser A} {f : A → Parser B} {L₁ L₂} →
  Accepts p L₁ → (∀ a → Accepts (f a) L₂) → Accepts (p >>= f) (L₁ · L₂)
accepts-bind sp sf = weaken (λ (xs , ys , _ , e , l₁ , l₂) → xs , ys , e , l₁ , l₂) (bind-sound sp sf)

-- A language widened to one containing it.
accepts-weaken : ∀ {A : Set} {p : Parser A} {L₁ L₂ : List Char → Set} →
  (∀ {cs} → L₁ cs → L₂ cs) → Accepts p L₁ → Accepts p L₂
accepts-weaken f = weaken f

-- A choice between two parsers both in one language.
if-accepts : ∀ {A : Set} (b : Bool) {p q : Parser A} {L} → Accepts p L → Accepts q L →
  Accepts (Data.Bool.if b then p else q) L
if-accepts true  sp sq = sp
if-accepts false sp sq = sq

-- A choice between two parsers in one language.
accepts-or : ∀ {A : Set} {p q : Parser A} {L} → Accepts p L → Accepts q L → Accepts (p <|> q) L
accepts-or sp sq = weaken (λ { (inj₁ l) → l ; (inj₂ l) → l }) (alt-sound sp sq)

-- `eof` then a value: nothing consumed, nothing left.
private
  eof-then : ∀ {A : Set} (x : A) pos input r →
    proj₂ ((eof >>= λ _ → pure x) pos input) ≡ just r → input ≡ [] × remaining r ≡ []
  eof-then x pos [] .(mkResult x pos []) refl = refl , refl
  eof-then x pos (_ ∷ _) r ()

-- A parser followed by the end of the input accepts its whole input.
before-eof : ∀ {A : Set} {p : Parser A} {L : List Char → Set} → Accepts p L →
  ∀ pos input r → proj₂ ((p <* eof) pos input) ≡ just r → L input
before-eof {p = p} {L} sp pos input r eq with p pos input in e₁
... | w , just r₁ with (eof >>= λ _ → pure (value r₁)) (position r₁) (remaining r₁) in e₂
...   | w′ , just r₂ with eof-then (value r₁) (position r₁) (remaining r₁) r₂ (cong proj₂ e₂)
                       | split sp pos input r₁ (cong proj₂ e₁)
...     | rest≡[] , _ | cs , i , l = subst L (sym (trans i (trans (cong (cs ++_) rest≡[]) (++-identityʳ cs)))) l
