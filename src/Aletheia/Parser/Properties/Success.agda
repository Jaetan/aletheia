-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- How a combinator's outcome follows from its parts' outcomes.
--
-- Stated on the outcome (`proj₂`), the level every read-back proof uses: a
-- success of the parts gives the success of the whole, and a failure of the
-- first part, or of every alternative, gives its failure.
module Aletheia.Parser.Properties.Success where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Aletheia.Parser.Combinators using (Parser; mkResult; advancePosition; advancePositions; pure; _>>=_; _<$>_; _<*>_; _<|>_; _*>_; _<*_; satisfy; optional; many; manyHelper; samePosᵇ)
open import Aletheia.Parser.Position.Properties using (samePosᵇ-advances)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (_++_; length; map)
open import Data.List.Properties using (++-assoc; length-++)
open import Data.Nat using (_≤_; _<_; suc)
open import Data.Nat.Properties using (≤-pred; ≤-trans; ≤-refl; +-monoˡ-≤)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; subst)

bind-just : ∀ {A B : Set} (p : Parser A) (f : A → Parser B) pos input {a pos₁ in₁ r} →
  proj₂ (p pos input) ≡ just (mkResult a pos₁ in₁) → proj₂ (f a pos₁ in₁) ≡ just r →
  proj₂ ((p >>= f) pos input) ≡ just r
bind-just p f pos input {a} {pos₁} {in₁} e₁ e₂ with p pos input | e₁
... | w , just .(mkResult a pos₁ in₁) | refl with f a pos₁ in₁ | e₂
...   | w′ , just r | refl = refl

bind-nothing : ∀ {A B : Set} (p : Parser A) (f : A → Parser B) pos input →
  proj₂ (p pos input) ≡ nothing → proj₂ ((p >>= f) pos input) ≡ nothing
bind-nothing p f pos input e with p pos input | e
... | w , nothing | refl = refl

map-just : ∀ {A B : Set} (g : A → B) (p : Parser A) pos input {a pos₁ in₁} →
  proj₂ (p pos input) ≡ just (mkResult a pos₁ in₁) →
  proj₂ ((g <$> p) pos input) ≡ just (mkResult (g a) pos₁ in₁)
map-just g p pos input {a} {pos₁} {in₁} e with p pos input | e
... | w , just .(mkResult a pos₁ in₁) | refl = refl

map-nothing : ∀ {A B : Set} (g : A → B) (p : Parser A) pos input →
  proj₂ (p pos input) ≡ nothing → proj₂ ((g <$> p) pos input) ≡ nothing
map-nothing g p pos input e with p pos input | e
... | w , nothing | refl = refl

ap-just : ∀ {A B : Set} (pf : Parser (A → B)) (px : Parser A) pos input {g a pos₁ in₁ pos₂ in₂} →
  proj₂ (pf pos input) ≡ just (mkResult g pos₁ in₁) →
  proj₂ (px pos₁ in₁) ≡ just (mkResult a pos₂ in₂) →
  proj₂ ((pf <*> px) pos input) ≡ just (mkResult (g a) pos₂ in₂)
ap-just pf px pos input {g} {a} {pos₁} {in₁} {pos₂} {in₂} e₁ e₂ with pf pos input | e₁
... | w , just .(mkResult g pos₁ in₁) | refl with (g <$> px) pos₁ in₁ | map-just g px pos₁ in₁ e₂
...   | w′ , just .(mkResult (g a) pos₂ in₂) | refl = refl

ap-nothing : ∀ {A B : Set} (pf : Parser (A → B)) (px : Parser A) pos input →
  proj₂ (pf pos input) ≡ nothing → proj₂ ((pf <*> px) pos input) ≡ nothing
ap-nothing pf px pos input e with pf pos input | e
... | w , nothing | refl = refl

then-just : ∀ {A B : Set} (p : Parser A) (q : Parser B) pos input {a pos₁ in₁ r} →
  proj₂ (p pos input) ≡ just (mkResult a pos₁ in₁) → proj₂ (q pos₁ in₁) ≡ just r →
  proj₂ ((p *> q) pos input) ≡ just r
then-just p q pos input e₁ e₂ = bind-just p (λ _ → q) pos input e₁ e₂

before-just : ∀ {A B : Set} (p : Parser A) (q : Parser B) pos input {a pos₁ in₁ b pos₂ in₂} →
  proj₂ (p pos input) ≡ just (mkResult a pos₁ in₁) → proj₂ (q pos₁ in₁) ≡ just (mkResult b pos₂ in₂) →
  proj₂ ((p <* q) pos input) ≡ just (mkResult a pos₂ in₂)
before-just p q pos input {a} e₁ e₂ =
  bind-just p (λ x → q >>= λ _ → pure x) pos input e₁ (bind-just q (λ _ → pure a) _ _ e₂ refl)

alt-left : ∀ {A : Set} (p q : Parser A) pos input {r} →
  proj₂ (p pos input) ≡ just r → proj₂ ((p <|> q) pos input) ≡ just r
alt-left p q pos input {r} e with p pos input | e
... | w , just .r | refl = refl

alt-right : ∀ {A : Set} (p q : Parser A) pos input →
  proj₂ (p pos input) ≡ nothing → proj₂ ((p <|> q) pos input) ≡ proj₂ (q pos input)
alt-right p q pos input e with p pos input | e
... | w , nothing | refl with q pos input
...   | w′ , out = refl

satisfy-just : ∀ (P : Char → Bool) pos c cs → P c ≡ true →
  proj₂ (satisfy P pos (c ∷ cs)) ≡ just (mkResult c (advancePosition pos c) cs)
satisfy-just P pos c cs e with P c | e
... | true | refl = refl

satisfy-nothing : ∀ (P : Char → Bool) pos c cs → P c ≡ false → proj₂ (satisfy P pos (c ∷ cs)) ≡ nothing
satisfy-nothing P pos c cs e with P c | e
... | false | refl = refl

satisfy-end : ∀ (P : Char → Bool) pos → proj₂ (satisfy P pos []) ≡ nothing
satisfy-end P pos = refl

optional-nothing : ∀ {A : Set} (p : Parser A) pos input →
  proj₂ (p pos input) ≡ nothing → proj₂ (optional p pos input) ≡ just (mkResult nothing pos input)
optional-nothing p pos input e = alt-right (just <$> p) (pure nothing) pos input (map-nothing just p pos input e)

optional-just : ∀ {A : Set} (p : Parser A) pos input {a pos₁ in₁} →
  proj₂ (p pos input) ≡ just (mkResult a pos₁ in₁) →
  proj₂ (optional p pos input) ≡ just (mkResult (just a) pos₁ in₁)
optional-just p pos input e = alt-left (just <$> p) (pure nothing) pos input (map-just just p pos input e)

-- ============================================================================
-- REPETITION
-- ============================================================================

-- A list written by `enc`, each element in front of the text after it.
encodeAll : ∀ {A : Set} → (A → List Char → List Char) → List A → List Char → List Char
encodeAll enc []       rest = rest
encodeAll enc (x ∷ xs) rest = enc x (encodeAll enc xs rest)

-- `p` reads back each element `enc` writes as the element's image under
-- `f`, each element writing at least one character in front of whatever
-- follows it, and fails on `stop`.
data Reads {A B : Set} (p : Parser B) (enc : A → List Char → List Char) (f : A → B) (stop : List Char) :
           List A → Set where
  reads-none : (∀ pos → proj₂ (p pos stop) ≡ nothing) → Reads p enc f stop []
  reads-more : ∀ {x xs} →
    (∀ pos → proj₂ (p pos (enc x (encodeAll enc xs stop)))
               ≡ just (mkResult (f x) (advancePositions pos (enc x [])) (encodeAll enc xs stop))) →
    (∀ rest → enc x rest ≡ enc x [] ++ rest) → 0 < length (enc x []) →
    Reads p enc f stop xs → Reads p enc f stop (x ∷ xs)

advancePositions-++ : ∀ pos xs ys → advancePositions pos (xs ++ ys) ≡ advancePositions (advancePositions pos xs) ys
advancePositions-++ pos []       ys = refl
advancePositions-++ pos (x ∷ xs) ys = advancePositions-++ (advancePosition pos x) xs ys

-- The elements' characters split from what follows them.
reads-split : ∀ {A B : Set} {p : Parser B} {enc f stop xs} → Reads {A} p enc f stop xs →
  ∀ rest → encodeAll enc xs rest ≡ encodeAll enc xs [] ++ rest
reads-split (reads-none _) rest = refl
reads-split {enc = enc} {xs = x ∷ xs} (reads-more _ split _ r) rest =
  trans (cong (enc x) (reads-split r rest))
        (trans (split (encodeAll enc xs [] ++ rest))
               (trans (sym (++-assoc (enc x []) (encodeAll enc xs []) rest))
                      (cong (_++ rest) (sym (split (encodeAll enc xs []))))))

private
  length-step : ∀ (xs ys : List Char) {n} → 0 < length xs → length (xs ++ ys) ≤ suc n → length ys ≤ n
  length-step xs ys {n} ne len =
    ≤-pred (≤-trans (+-monoˡ-≤ (length ys) ne) (subst (_≤ suc n) (length-++ xs) len))

  length-nonzero : ∀ (xs ys : List Char) → 0 < length xs → length (xs ++ ys) ≤ 0 → ⊥
  length-nonzero (_ ∷ _) ys _ ()

manyHelper-readback : ∀ {A B : Set} {p : Parser B} {enc f stop xs} → Reads {A} p enc f stop xs →
  ∀ pos bound → length (encodeAll enc xs stop) ≤ length bound →
  proj₂ (manyHelper p pos (encodeAll enc xs stop) bound)
    ≡ just (mkResult (map f xs) (advancePositions pos (encodeAll enc xs [])) stop)
manyHelper-readback (reads-none f) pos [] _ = refl
manyHelper-readback {p = p} {stop = stop} (reads-none f) pos (_ ∷ bound) _ with p pos stop | f pos
... | w , nothing | refl = refl
manyHelper-readback {enc = enc} {stop = stop} {x ∷ xs} (reads-more e split ne r) pos [] len =
  ⊥-elim (length-nonzero (enc x []) (encodeAll enc xs stop) ne (subst (λ z → length z ≤ 0) (split _) len))
manyHelper-readback {p = p} {enc} {f} {stop} {x ∷ xs} (reads-more e split ne r) pos (_ ∷ bound) len
  with p pos (enc x (encodeAll enc xs stop)) | e pos
... | w , just .(mkResult (f x) (advancePositions pos (enc x [])) (encodeAll enc xs stop)) | refl
  with samePosᵇ (advancePositions pos (enc x [])) pos | samePosᵇ-advances pos (enc x []) ne
... | false | refl
  with manyHelper p (advancePositions pos (enc x [])) (encodeAll enc xs stop) bound
     | manyHelper-readback r (advancePositions pos (enc x [])) bound
         (length-step (enc x []) (encodeAll enc xs stop) ne (subst (λ z → length z ≤ suc (length bound)) (split _) len))
... | w′ , just .(mkResult (map f xs) (advancePositions (advancePositions pos (enc x [])) (encodeAll enc xs [])) stop) | refl =
  cong (λ q → just (mkResult (f x ∷ map f xs) q stop))
       (sym (trans (cong (advancePositions pos) (split (encodeAll enc xs [])))
                   (advancePositions-++ pos (enc x []) (encodeAll enc xs []))))

-- `many p` reads back every element `p` reads, and stops where `p` fails.
many-readback : ∀ {A B : Set} {p : Parser B} {enc f stop xs} → Reads {A} p enc f stop xs → ∀ pos →
  proj₂ (many p pos (encodeAll enc xs stop)) ≡ just (mkResult (map f xs) (advancePositions pos (encodeAll enc xs [])) stop)
many-readback {enc = enc} {stop = stop} {xs} r pos = manyHelper-readback r pos (encodeAll enc xs stop) ≤-refl

-- ============================================================================
-- READING A KNOWN TEXT
-- ============================================================================

-- From any position, `p` reads `t` in front of `r` as `a`, leaving `r`.
record ReadsText {A : Set} (p : Parser A) (t : List Char) (a : A) (r : List Char) : Set where
  constructor reading
  field
    readsAt : ∀ pos → proj₂ (p pos (t ++ r)) ≡ just (mkResult a (advancePositions pos t) r)

open ReadsText public

then-reads : ∀ {A B : Set} {p : Parser A} {q : Parser B} {t₁ t₂ a b r} →
  ReadsText p t₁ a (t₂ ++ r) → ReadsText q t₂ b r → ReadsText (p *> q) (t₁ ++ t₂) b r
then-reads {p = p} {q} {t₁} {t₂} {b = b} {r} rp rq = reading λ pos →
  subst (λ input → proj₂ ((p *> q) pos input) ≡ just (mkResult b (advancePositions pos (t₁ ++ t₂)) r))
        (sym (++-assoc t₁ t₂ r))
        (trans (then-just p q pos (t₁ ++ t₂ ++ r) (readsAt rp pos) (readsAt rq (advancePositions pos t₁)))
               (cong (λ q′ → just (mkResult b q′ r)) (sym (advancePositions-++ pos t₁ t₂))))

before-reads : ∀ {A B : Set} {p : Parser A} {q : Parser B} {t₁ t₂ a b r} →
  ReadsText p t₁ a (t₂ ++ r) → ReadsText q t₂ b r → ReadsText (p <* q) (t₁ ++ t₂) a r
before-reads {p = p} {q} {t₁} {t₂} {a} {r = r} rp rq = reading λ pos →
  subst (λ input → proj₂ ((p <* q) pos input) ≡ just (mkResult a (advancePositions pos (t₁ ++ t₂)) r))
        (sym (++-assoc t₁ t₂ r))
        (trans (before-just p q pos (t₁ ++ t₂ ++ r) (readsAt rp pos) (readsAt rq (advancePositions pos t₁)))
               (cong (λ q′ → just (mkResult a q′ r)) (sym (advancePositions-++ pos t₁ t₂))))

ap-reads : ∀ {A B : Set} {pf : Parser (A → B)} {px : Parser A} {t₁ t₂ g a r} →
  ReadsText pf t₁ g (t₂ ++ r) → ReadsText px t₂ a r → ReadsText (pf <*> px) (t₁ ++ t₂) (g a) r
ap-reads {pf = pf} {px} {t₁} {t₂} {g} {a} {r} rf rx = reading λ pos →
  subst (λ input → proj₂ ((pf <*> px) pos input) ≡ just (mkResult (g a) (advancePositions pos (t₁ ++ t₂)) r))
        (sym (++-assoc t₁ t₂ r))
        (trans (ap-just pf px pos (t₁ ++ t₂ ++ r) (readsAt rf pos) (readsAt rx (advancePositions pos t₁)))
               (cong (λ q′ → just (mkResult (g a) q′ r)) (sym (advancePositions-++ pos t₁ t₂))))

map-reads : ∀ {A B : Set} {g : A → B} {p : Parser A} {t a r} → ReadsText p t a r → ReadsText (g <$> p) t (g a) r
map-reads {g = g} {p} {t} {r = r} rp = reading λ pos → map-just g p pos (t ++ r) (readsAt rp pos)

alt-left-reads : ∀ {A : Set} {p q : Parser A} {t a r} → ReadsText p t a r → ReadsText (p <|> q) t a r
alt-left-reads {p = p} {q} {t} {r = r} rp = reading λ pos → alt-left p q pos (t ++ r) (readsAt rp pos)

alt-right-reads : ∀ {A : Set} {p q : Parser A} {t a r} →
  (∀ pos → proj₂ (p pos (t ++ r)) ≡ nothing) → ReadsText q t a r → ReadsText (p <|> q) t a r
alt-right-reads {p = p} {q} {t} {r = r} fp rq = reading λ pos → trans (alt-right p q pos (t ++ r) (fp pos)) (readsAt rq pos)

-- A text read differently spelled.
reads-text : ∀ {A : Set} {p : Parser A} {t t′ a r} → t ≡ t′ → ReadsText p t a r → ReadsText p t′ a r
reads-text refl rp = rp

reads-value : ∀ {A : Set} {p : Parser A} {t a a′ r} → a ≡ a′ → ReadsText p t a r → ReadsText p t a′ r
reads-value refl rp = rp

many-reads : ∀ {A B : Set} {p : Parser B} {enc f stop xs} → Reads {A} p enc f stop xs →
  ReadsText (many p) (encodeAll enc xs []) (map f xs) stop
many-reads {p = p} {enc} {f} {stop} {xs} r = reading λ pos →
  subst (λ input → proj₂ (many p pos input) ≡ just (mkResult (map f xs) (advancePositions pos (encodeAll enc xs [])) stop))
        (reads-split r stop) (many-readback r pos)

-- A read stated on the input written out, here the text followed by the rest.
reads-from : ∀ {A : Set} {p : Parser A} {t v r i} → i ≡ t ++ r →
  (∀ pos → proj₂ (p pos i) ≡ just (mkResult v (advancePositions pos t) r)) → ReadsText p t v r
reads-from refl f = reading f

pure-reads : ∀ {A : Set} (a : A) {r} → ReadsText (pure a) [] a r
pure-reads a = reading λ pos → refl
