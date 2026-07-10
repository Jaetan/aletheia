-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Per-primitive roundtrip lemmas for the DBC text-format parser.
--
-- The module provides `parseIdentifier-roundtrip` plus Tier A
-- (char / keyword dispatch — no `many`, no embedded sub-parser) and
-- Tier B (internal `many` / one embedded sub-parser):
--
--   Tier A:
--     * `parseByteOrderDigit-roundtrip`
--     * `parseSignFlag-roundtrip`
--
--   Tier B:
--     * `parseStringLit-roundtrip`              (escape body)
--     * `parseMuxMarker-roundtrip`              (inverse targets
--       `MuxMarker`, NOT `SignalPresence` — see project memory)
--
-- The `parseOptionalStandardScope` / `parseRelScopeWS`
-- / `parseStringType` per-tag roundtrips were dropped — the universal
-- Format DSL roundtrip in `Format/AttrDef.agda` subsumes them, and the
-- only consumers were the now-rewritten `Properties/Attributes/{Type,
-- Def}.agda`.  `ATInt` / `ATFloat` / `ATHex` / `ATEnum` and
-- `SignalPresence` are reclassified as per-line-construct
-- payloads with internal WS separation or post-parse context
-- resolution, not primitives.  See `memory/project_b3d_universal_
-- proof.md`.
module Aletheia.DBC.TextParser.Properties.Primitives where

open import Data.Bool using (Bool; true; false; T; _∧_)
open import Data.Char using (Char)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_) renaming (_++_ to _++ₗ_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₂)
open import Data.String using (String; toList)
open import Data.Unit using ()
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Data.Char.Base using (_≈ᵇ_; toℕ)
open import Data.Char using () renaming (_≟_ to _≟ᶜ_)
open import Data.Char.Properties using (toℕ-injective)
open import Data.List using (foldr; length)
open import Data.List.Properties using () renaming (++-assoc to ++ₗ-assoc)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≡⇒≡ᵇ; ≡ᵇ⇒≡; m≤n⇒m≤1+n; m≤m+n; ≤-trans)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (⌊_⌋; yes; no)
open import Relation.Nullary using (¬_)

open import Aletheia.Parser.Combinators using
  (Parser; Position; mkResult; advancePosition; advancePositions;
   pure; _>>=_; _<|>_; _*>_; _<$>_; satisfy; many; manyHelper;
   char; string; parseCharsSeq; sameLengthᵇ)
open import Aletheia.DBC.Identifier using
  (Identifier; mkIdentFromChars; mkIdentFromChars-on-valid;
   isIdentStart; isIdentCont; validIdentifierᵇ; allᵇ)
open import Aletheia.DBC.TextParser.Lexer using
  (parseIdentifier; buildIdent; fromMaybeIdent;
   parseStringLit; parseStringChar; parseWS; isHSpace)
open import Aletheia.DBC.TextFormatter.Emitter using
  (quoteStringLit-chars; escapeChar-chars)
-- Substrate.Unsafe is no longer imported here.
-- `mkIdentFromCharsUnsafe-on-valid` (which needed `fromList∘toList`)
-- becomes `mkIdentFromChars-on-valid` (axiom-free, via `T?` decision).
-- `parseStringLit-roundtrip` now takes `(cs : List Char)` and parses
-- back to the same `cs`, so the trailing `fromList∘toList s` cong step
-- is gone.  This module becomes axiom-free and lifts to `--safe`.
open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; ∷-stop; bind-just-step;
   manyHelper-satisfy-exhaust-many; sameLengthᵇ-cons;
   advancePositions-++)
open import Aletheia.Prelude using (T→true)

-- ============================================================================
-- Probe 1 — decompose-valid
-- ============================================================================
--
-- `T (validIdentifierᵇ cs)` destructures into: `cs = h ∷ t`, the head
-- satisfies `isIdentStart`, and the tail is pointwise `isIdentCont`.
-- Empty list rejected by `validIdentifierᵇ [] = false → T false = ⊥`.

-- Helper: T (a ∧ b) → T a × T b  (stdlib has this but requires specific import)
private
  T-∧-split : ∀ {a b : Bool} → T (a ∧ b) → T a × T b
  T-∧-split {true}  {true}  _ = tt , tt
  T-∧-split {true}  {false} ()
  T-∧-split {false} {_}     ()

-- Helper: T (allᵇ p xs) → All (T ∘ p) xs
private
  T-allᵇ→All : ∀ (p : Char → Bool) (xs : List Char)
             → T (allᵇ p xs) → All (T ∘ p) xs
  T-allᵇ→All p []       _  = []
  T-allᵇ→All p (c ∷ cs) ab =
    let (pc , pcs) = T-∧-split {p c} {allᵇ p cs} ab
    in pc ∷ T-allᵇ→All p cs pcs

-- `validIdentifierᵇ (h ∷ t)` is now a 3-conjunct
-- `isIdentStart h ∧ (allᵇ isIdentCont t ∧ length (h ∷ t) <ᵇ suc max-…)`.
-- Two splits unpack the start-char and cont-list witnesses; the length
-- bound is preserved by the Identifier record's `valid` field for callers
-- that need it (decompose-valid drops it because no existing consumer
-- threads it through).  Implicit args inferred from `valid`'s type.
decompose-valid : ∀ (cs : List Char) → T (validIdentifierᵇ cs)
  → ∃[ h ] ∃[ t ]
    (cs ≡ h ∷ t) × T (isIdentStart h) × All (T ∘ isIdentCont) t
decompose-valid []       ()
decompose-valid (h ∷ t) valid =
  let (ph , rest) = T-∧-split valid
      (pt , _)    = T-∧-split rest
  in h , t , refl , ph , T-allᵇ→All isIdentCont t pt

-- ============================================================================
-- Probe 2 — mkIdentFromChars on a valid Identifier's char list
-- ============================================================================
--
-- `mkIdentFromChars-on-valid` now lives in `Aletheia.DBC.Identifier` (its
-- single home alongside `mkIdentFromChars` — cat 27 lemma dedup; also consumed
-- by `LTL.JSON.Properties` for the predicate roundtrip) and is
-- imported above.  Axiom-free: matches the `with T? (validIdentifierᵇ name)`
-- in the function definition; `yes` closes via `T-irrelevant`, `no` is absurd.

-- ============================================================================
-- Probe 3 — position alignment (decomposition consistency)
-- ============================================================================
--
-- `Identifier.name i` IS `h ∷ t` where (h, t) come from `decompose-valid`
-- applied to `Identifier.valid i`.  Follows by refl from the decomposition's
-- first output equation.

decompose-valid-matches-name : ∀ (i : Identifier)
  → let cs = Identifier.name i
        d  = decompose-valid cs (Identifier.valid i)
        h  = Data.Product.proj₁ d
        t  = Data.Product.proj₁ (Data.Product.proj₂ d)
    in cs ≡ h ∷ t
decompose-valid-matches-name i
  with decompose-valid (Identifier.name i) (Identifier.valid i)
... | _ , _ , eq , _ , _ = eq

-- ============================================================================
-- Probe 4 — satisfy-success-T
-- ============================================================================
--
-- `satisfy P` succeeds and consumes one char given a `T (P h)` witness.
-- Mirrors the pattern used by `some-satisfy-prefix` in
-- `DecRatParse.Properties` — `rewrite T→true ph` unblocks the internal
-- `with P h` in `satisfy`'s body, at which point `refl` closes the goal.

satisfy-success-T : ∀ (P : Char → Bool) (pos : Position) (h : Char) (cs : List Char)
  → T (P h)
  → proj₂ (satisfy P pos (h ∷ cs)) ≡ just (mkResult h (advancePosition pos h) cs)
satisfy-success-T P pos h cs ph rewrite T→true ph = refl

-- ============================================================================
-- Probe 5 — buildIdent-eq
-- ============================================================================
--
-- `buildIdent h t ≡ pure i` follows by `cong fromMaybeIdent` from the
-- `mkIdentFromChars (h ∷ t) ≡ just i` equation (given by
-- `mkIdentFromChars-on-valid` composed with `sym cs-eq` from
-- `decompose-valid`).  The Lexer refactor (split into
-- `buildIdent h t = fromMaybeIdent (mkIdentFromChars (h ∷ t))`) is the
-- reason this closes as a one-liner — a top-level `with` in `buildIdent`
-- would have hidden the Maybe from external rewriting.

buildIdent-eq : ∀ (h : Char) (t : List Char) (i : Identifier)
  → mkIdentFromChars (h ∷ t) ≡ just i
  → buildIdent h t ≡ pure i
buildIdent-eq _ _ _ eq = cong fromMaybeIdent eq

-- ============================================================================
-- parseIdentifier-roundtrip — composed theorem
-- ============================================================================
--
-- The main layer-2 Identifier lemma: parsing any valid Identifier's char
-- list concatenated with a stopping suffix returns that Identifier plus
-- the untouched suffix.  Structure mirrors
-- `DecRatParse/Properties.parseDecRat-roundtrip-+suc` — two
-- `bind-just-step`s + one final `buildIdent-eq`-applied step, chained
-- via `trans`.  `subst` on `sym cs-eq` lifts the concrete-shape proof
-- (`h ∷ t` form) back to the abstract `Identifier.name i` form the
-- public theorem advertises.  `Identifier.name : List Char`
-- means the public statement is in terms of the same `List Char`
-- substrate the parser machinery operates on — no `toList` wrap needed.

-- Lift `All (T ∘ P) xs` to `All (λ c → P c ≡ true) xs` — the form
-- `manyHelper-satisfy-exhaust-many` demands.  Trivial pointwise `T→true`.
private
  T-All→≡true : ∀ {P : Char → Bool} {xs : List Char}
             → All (T ∘ P) xs
             → All (λ c → P c ≡ true) xs
  T-All→≡true []         = []
  T-All→≡true (px ∷ pxs) = T→true px ∷ T-All→≡true pxs

parseIdentifier-roundtrip : ∀ (pos : Position) (i : Identifier)
                              (suffix : List Char)
                            → SuffixStops isIdentCont suffix
                            → proj₂ (parseIdentifier pos
                                       (Identifier.name i ++ₗ suffix))
                              ≡ just (mkResult i
                                       (advancePositions pos
                                          (Identifier.name i))
                                       suffix)
parseIdentifier-roundtrip pos i suffix ss
  with decompose-valid (Identifier.name i) (Identifier.valid i)
... | h , t , cs-eq , start , conts =
      subst (λ cs → proj₂ (parseIdentifier pos (cs ++ₗ suffix))
                      ≡ just (mkResult i (advancePositions pos cs) suffix))
            (sym cs-eq)
            concrete-proof
  where
    pos' : Position
    pos' = advancePosition pos h

    pos'' : Position
    pos'' = advancePositions pos' t

    -- satisfy isIdentStart consumes h, advancing to pos' with tail t++suffix.
    step-satisfy :
      proj₂ (parseIdentifier pos ((h ∷ t) ++ₗ suffix))
      ≡ proj₂ ((many (satisfy isIdentCont) >>= λ t' → buildIdent h t')
                 pos' (t ++ₗ suffix))
    step-satisfy =
      bind-just-step (satisfy isIdentStart)
                     (λ h' → many (satisfy isIdentCont) >>=
                             λ t' → buildIdent h' t')
                     pos ((h ∷ t) ++ₗ suffix)
                     h pos' (t ++ₗ suffix)
                     (satisfy-success-T isIdentStart pos h (t ++ₗ suffix) start)

    -- many (satisfy isIdentCont) consumes t, advancing to pos'' with suffix.
    step-many :
      proj₂ ((many (satisfy isIdentCont) >>= λ t' → buildIdent h t')
               pos' (t ++ₗ suffix))
      ≡ proj₂ (buildIdent h t pos'' suffix)
    step-many =
      bind-just-step (many (satisfy isIdentCont))
                     (λ t' → buildIdent h t')
                     pos' (t ++ₗ suffix)
                     t pos'' suffix
                     (manyHelper-satisfy-exhaust-many isIdentCont pos' t suffix
                        (T-All→≡true conts) ss)

    -- buildIdent h t reduces via fromMaybeIdent (mkIdentFromChars (h ∷ t))
    -- = fromMaybeIdent (just i) = pure i, once we bridge through cs-eq and
    -- mkIdentFromChars-on-valid.
    mki-eq : mkIdentFromChars (h ∷ t) ≡ just i
    mki-eq = trans (cong mkIdentFromChars (sym cs-eq))
                   (mkIdentFromChars-on-valid i)

    step-build :
      proj₂ (buildIdent h t pos'' suffix)
      ≡ just (mkResult i pos'' suffix)
    step-build = cong (λ p → proj₂ (p pos'' suffix)) (buildIdent-eq h t i mki-eq)

    concrete-proof :
      proj₂ (parseIdentifier pos ((h ∷ t) ++ₗ suffix))
      ≡ just (mkResult i (advancePositions pos (h ∷ t)) suffix)
    concrete-proof = trans step-satisfy (trans step-many step-build)

-- ============================================================================
-- Tier A — single-char keyword dispatch
-- ============================================================================
--
-- `parseByteOrderDigit-roundtrip` and `parseSignFlag-roundtrip` were
-- moved to `Properties.Primitives.Bools`.  Pure value-only single-char
-- dispatch with no
-- helper dependencies — clean extraction.  Re-exported from
-- `Properties.agda` to keep the public API stable.

-- ============================================================================
-- Char equality — concrete char matches trivially, abstract needs reflexivity
-- ============================================================================

-- `_≈ᵇ_` is `toℕ c ≡ᵇ toℕ d`; reflexivity reduces definitionally on closed
-- chars but needs a lemma on an abstract `c`.  Thread through stdlib's
-- `≡⇒≡ᵇ` + `T→true`.

≈ᵇ-refl : ∀ (c : Char) → (c ≈ᵇ c) ≡ true
≈ᵇ-refl c = T→true (≡⇒≡ᵇ (toℕ c) (toℕ c) refl)

-- `char c` on input starting with exactly `c` consumes one char and
-- advances position.  `rewrite ≈ᵇ-refl c` unblocks the internal
-- `with c ≈ᵇ c` inside `satisfy`'s body, leaving `refl`.

char-matches : ∀ (c : Char) (pos : Position) (cs : List Char)
  → proj₂ (char c pos (c ∷ cs))
    ≡ just (mkResult c (advancePosition pos c) cs)
char-matches c pos cs rewrite ≈ᵇ-refl c = refl

-- ============================================================================
-- Tier A — `string` keyword helpers
-- ============================================================================

-- `string s` on input that begins with `toList s` succeeds and returns
-- `just (mkResult s (advancePositions pos (toList s)) suffix)`.
--
-- Proof pattern: induct on the char list `cs = toList s`, reducing the
-- internal `parseChars` recursion one char at a time.  Each step uses
-- definitional reduction of `char c` on `c ∷ rest`.  Factored out so
-- every scope / keyword primitive reuses it.

-- `parseCharsSeq cs` on input `cs ++ₗ suffix` succeeds, returning the
-- same list `cs` with the position advanced past every element.  Induct
-- on `cs`; each step uses `char-matches` to reduce the head char match
-- then recurses on the tail.
parseCharsSeq-success : ∀ (pos : Position) (cs : List Char)
                          (suffix : List Char)
  → proj₂ (parseCharsSeq cs pos (cs ++ₗ suffix))
    ≡ just (mkResult cs (advancePositions pos cs) suffix)
parseCharsSeq-success pos []       suffix = refl
parseCharsSeq-success pos (c ∷ cs) suffix =
  trans (bind-just-step (char c)
           (λ x → parseCharsSeq cs >>= λ xs → pure (x ∷ xs))
           pos (c ∷ cs ++ₗ suffix)
           c (advancePosition pos c) (cs ++ₗ suffix)
           (char-matches c pos (cs ++ₗ suffix)))
    (trans (bind-just-step (parseCharsSeq cs)
              (λ xs → pure (c ∷ xs))
              (advancePosition pos c) (cs ++ₗ suffix)
              cs (advancePositions (advancePosition pos c) cs) suffix
              (parseCharsSeq-success (advancePosition pos c) cs suffix))
       refl)

-- `string`-success lemma: `string s` on `toList s ++ₗ suffix` returns
-- `just (mkResult s (advancePositions pos (toList s)) suffix)`.
string-success : ∀ (pos : Position) (s : String) (suffix : List Char)
  → proj₂ (string s pos (toList s ++ₗ suffix))
    ≡ just (mkResult s (advancePositions pos (toList s)) suffix)
string-success pos s suffix =
  bind-just-step (parseCharsSeq (toList s))
                 (λ _ → pure s)
                 pos (toList s ++ₗ suffix)
                 (toList s) (advancePositions pos (toList s)) suffix
                 (parseCharsSeq-success pos (toList s) suffix)

-- `(string s *> pure v)` — the keyword-dispatch idiom used by every
-- scope / attr-type-tag parser.  Composes `string-success` with a
-- single `bind-just-step`.
string-*>-success : ∀ {V : Set} (pos : Position) (s : String) (v : V)
                      (suffix : List Char)
  → proj₂ ((string s *> pure v) pos (toList s ++ₗ suffix))
    ≡ just (mkResult v (advancePositions pos (toList s)) suffix)
string-*>-success pos s v suffix =
  bind-just-step (string s)
                 (λ _ → pure v)
                 pos (toList s ++ₗ suffix)
                 s (advancePositions pos (toList s)) suffix
                 (string-success pos s suffix)

-- ============================================================================
-- <|> reduction lemmas
-- ============================================================================

-- `p <|> q`'s OUTCOME reduces to `q`'s when `p` fails.  Outcome level
-- (`proj₂`) only: under furthest-failure merging the full pair carries
-- `maxₚ` of both arms' watermarks, so pair-level equality is false.
-- The inner `with` on `q pos input` exposes the same outcome variable
-- on both sides.
alt-right-nothing : ∀ {A : Set} (p q : Parser A) (pos : Position)
                      (input : List Char)
  → proj₂ (p pos input) ≡ nothing
  → proj₂ ((p <|> q) pos input) ≡ proj₂ (q pos input)
alt-right-nothing p q pos input eq with p pos input | eq
... | w , nothing | refl with q pos input
...   | w' , out = refl

-- `p <|> q` reduces to `just r` when `p` returns `just r` (left wins).
alt-left-just : ∀ {A : Set} (p q : Parser A) (pos : Position)
                  (input : List Char) r
  → proj₂ (p pos input) ≡ just r
  → proj₂ ((p <|> q) pos input) ≡ just r
alt-left-just p q pos input r eq with p pos input | eq
... | w , just .r | refl = refl

-- Bind propagates failure outward.
bind-nothing : ∀ {A B : Set} (p : Parser A) (f : A → Parser B)
                 (pos : Position) (input : List Char)
  → proj₂ (p pos input) ≡ nothing
  → proj₂ ((p >>= f) pos input) ≡ nothing
bind-nothing p f pos input eq with p pos input | eq
... | w , nothing | refl = refl

-- Functor map propagates failure outward.  Mirror of `bind-nothing`
-- for `_<$>_`.  Both `>>=` and `<$>` are defined by `with p pos input`,
-- so the proof shape is identical.
map-nothing : ∀ {A B : Set} (g : A → B) (p : Parser A)
                (pos : Position) (input : List Char)
  → proj₂ (p pos input) ≡ nothing
  → proj₂ ((g <$> p) pos input) ≡ nothing
map-nothing g p pos input eq with p pos input | eq
... | w , nothing | refl = refl

-- ============================================================================
-- parseWS on "one horizontal space then non-space suffix"
-- ============================================================================

-- `parseWS = some (satisfy isHSpace) = (λ x xs → x ∷ xs) <$> satisfy … <*> many …`.
-- On input `' ' ∷ suffix` with `SuffixStops isHSpace suffix`, `satisfy`
-- consumes the space, `many` returns empty (base case: the suffix's head
-- fails `isHSpace`), and the `<$>`/`<*>` chain wraps the result as
-- `[' ']`.
parseWS-one-space : ∀ (pos : Position) (suffix : List Char)
  → SuffixStops isHSpace suffix
  → proj₂ (parseWS pos (' ' ∷ suffix))
    ≡ just (mkResult (' ' ∷ [])
                     (advancePosition pos ' ') suffix)
parseWS-one-space pos suffix ss
  with manyHelper (satisfy isHSpace) (advancePosition pos ' ')
         suffix (length suffix)
     | manyHelper-satisfy-exhaust-many isHSpace
         (advancePosition pos ' ') [] suffix [] ss
... | w , just r | refl = refl

-- `parseWS` succeeds with a singleton `'\t'` on a `'\t'`-led input whose
-- continuation is hspace-stopped.  Mirror of `parseWS-one-space` for the
-- tab variant; used by the NS_ keyword-line bridge (the formatter emits
-- `'\t'` for indent) and by the Format DSL's `wsCanonTab` constructor.
parseWS-one-tab : ∀ (pos : Position) (suffix : List Char)
  → SuffixStops isHSpace suffix
  → proj₂ (parseWS pos ('\t' ∷ suffix))
    ≡ just (mkResult ('\t' ∷ [])
                     (advancePosition pos '\t') suffix)
parseWS-one-tab pos suffix ss
  with manyHelper (satisfy isHSpace) (advancePosition pos '\t')
         suffix (length suffix)
     | manyHelper-satisfy-exhaust-many isHSpace
         (advancePosition pos '\t') [] suffix [] ss
... | w , just r | refl = refl

-- ============================================================================
-- Tier B — string literal roundtrip
-- ============================================================================
--
-- `quoteStringLit-chars cs = '"' ∷ (body) ++ₗ '"' ∷ []` where the body
-- is `foldr` expanding each `"` to `""`.  The parser consumes the
-- opening quote, `many parseStringChar` expands back to the original
-- `cs`, then consumes the closing quote.
-- `parseStringLit : Parser (List Char)` returns `cs` directly (no
-- `fromList`); the trailing `fromList∘toList` axiom step is gone.
--
-- Bool-form precondition: `SuffixStops (λ c → c ≈ᵇ '"') suffix`.  We
-- pick `_≈ᵇ_` because every concrete char-dispatch inside the body
-- reduces through `char '"'` (which uses `_≈ᵇ_` via `satisfy`).  The
-- ambient `escapeChar-chars` + `satisfy (not ⌊ _ ≟ᶜ '"' ⌋)` branches
-- use `_≟ᶜ_`; we bridge once with `≈ᵇ-false→≟ᶜ-false`.

-- Structural decomposition of the escape-body produced by the
-- `foldr` inside `quoteStringLit-chars`.
escape-body-chars : List Char → List Char
escape-body-chars []       = []
escape-body-chars (c ∷ cs) = escapeChar-chars c ++ₗ escape-body-chars cs

-- `quoteStringLit-chars` rewritten as explicit open quote + escape
-- body + close quote.  Structural induction on `cs`; the `cons` step
-- uses `++ₗ-assoc` to relocate the close-quote seed from inside the
-- `foldr` into the list-append chain.
quoteStringLit-chars-shape : ∀ (cs : List Char)
  → quoteStringLit-chars cs
    ≡ '"' ∷ escape-body-chars cs ++ₗ '"' ∷ []
quoteStringLit-chars-shape cs = cong ('"' ∷_) (shape cs)
  where
    shape : ∀ (xs : List Char)
      → foldr (λ c acc → escapeChar-chars c ++ₗ acc) ('"' ∷ []) xs
        ≡ escape-body-chars xs ++ₗ '"' ∷ []
    shape []       = refl
    shape (x ∷ xs) =
      trans (cong (λ acc → escapeChar-chars x ++ₗ acc) (shape xs))
            (sym (++ₗ-assoc (escapeChar-chars x)
                    (escape-body-chars xs) ('"' ∷ [])))

-- ============================================================================
-- Char (in)equality bridges for the string-literal proofs
-- ============================================================================

-- `c ≢ d` ⇒ `⌊ c ≟ᶜ d ⌋ ≡ false`.  Routine case-split on decidability.
⌊⌋-false-of-≢ : ∀ {c d : Char} → ¬ (c ≡ d) → ⌊ c ≟ᶜ d ⌋ ≡ false
⌊⌋-false-of-≢ {c} {d} c≢d with c ≟ᶜ d
... | yes c≡d = ⊥-elim (c≢d c≡d)
... | no  _   = refl

-- `c ≢ d` ⇒ `(c ≈ᵇ d) ≡ false`.  Bridge through the primitive
-- `toℕ-injective`: if `c ≈ᵇ d = true`, then `toℕ c ≡ᵇ toℕ d = true`,
-- hence `toℕ c ≡ toℕ d` (via stdlib `≡ᵇ⇒≡`), hence `c ≡ d` — which
-- contradicts the precondition.
≈ᵇ-false-of-≢ : ∀ {c d : Char} → ¬ (c ≡ d) → (c ≈ᵇ d) ≡ false
≈ᵇ-false-of-≢ {c} {d} c≢d with c ≈ᵇ d in eq
... | false = refl
... | true  =
      ⊥-elim (c≢d (toℕ-injective c d
                     (≡ᵇ⇒≡ (toℕ c) (toℕ d) (subst T (sym eq) tt))))
  where open import Data.Bool using (T)


-- ============================================================================
-- parseStringChar probes
-- ============================================================================

-- Escape pair: closed-char dispatch reduces to refl.  `string "\"\""`
-- matches the two concrete `"` characters via the parseCharsSeq
-- definitional expansion; the outer `<|>` returns via `alt-left-just`
-- (definitionally).
parseStringChar-escape : ∀ (pos : Position) (rest : List Char)
  → proj₂ (parseStringChar pos ('"' ∷ '"' ∷ rest))
    ≡ just (mkResult '"'
             (advancePosition (advancePosition pos '"') '"') rest)
parseStringChar-escape _ _ = refl

-- Non-quote literal: `string "\"\""` branch fails (char '"' on `c ∷ rest`
-- with `c ≢ '"'` fails), so `<|>` falls to `satisfy (not ⌊ _ ≟ᶜ '"' ⌋)`.
-- With `⌊ c ≟ᶜ '"' ⌋ ≡ false`, `not false = true`, and `satisfy`
-- succeeds with the head char.
parseStringChar-literal : ∀ (pos : Position) (c : Char) (rest : List Char)
  → ¬ (c ≡ '"')
  → proj₂ (parseStringChar pos (c ∷ rest))
    ≡ just (mkResult c (advancePosition pos c) rest)
parseStringChar-literal pos c rest c≢quote
  rewrite ≈ᵇ-false-of-≢ {c} {'"'} c≢quote
        | ⌊⌋-false-of-≢ {c} {'"'} c≢quote = refl

-- Fail at closing quote: input `'"' ∷ suffix` with suffix not starting
-- with `"`.  Both `<|>` branches fail:
--   * `string "\"\""` tries `char '"'` (succeeds at position 0),
--     then `char '"'` on `suffix`.  `suffix` first-char isn't `"`
--     (via `SuffixStops _≈ᵇ_ `) → fails.
--   * `satisfy (not ⌊ '"' ≟ᶜ '"' ⌋)` = `satisfy (not true)` =
--     `satisfy false-predicate` → fails on any non-empty input.
parseStringChar-fail-at-close : ∀ (pos : Position) (suffix : List Char)
  → SuffixStops (λ c → c ≈ᵇ '"') suffix
  → proj₂ (parseStringChar pos ('"' ∷ suffix)) ≡ nothing
parseStringChar-fail-at-close pos [] _ = refl
parseStringChar-fail-at-close pos (c ∷ suffix) (∷-stop ≈false)
  rewrite ≈false = refl

-- `escape-body-chars` dispatch helpers: the `c = '"'` branch emits
-- `'"' ∷ '"' ∷ []` (escape pair); the non-quote branch emits `c ∷ []`.
escape-body-chars-quote : ∀ (cs : List Char)
  → escape-body-chars ('"' ∷ cs) ≡ '"' ∷ '"' ∷ escape-body-chars cs
escape-body-chars-quote _ = refl

escape-body-chars-nonquote : ∀ (c : Char) (cs : List Char)
  → ¬ (c ≡ '"')
  → escape-body-chars (c ∷ cs) ≡ c ∷ escape-body-chars cs
escape-body-chars-nonquote c cs c≢quote
  rewrite ⌊⌋-false-of-≢ {c} {'"'} c≢quote = refl

-- Cons-by-2 progress witness for `manyHelper`'s `sameLengthᵇ` check.
-- Structurally recursive on the tail; mirrors `sameLengthᵇ-cons` in
-- `DecRatParse.Properties` (which covers the cons-by-1 case).
private
  sameLengthᵇ-cons-cons : ∀ {A : Set} (x y : A) (l : List A)
    → sameLengthᵇ (x ∷ y ∷ l) l ≡ false
  sameLengthᵇ-cons-cons x y []       = refl
  sameLengthᵇ-cons-cons x y (z ∷ zs) = sameLengthᵇ-cons-cons y z zs

-- ============================================================================
-- `manyHelper parseStringChar` workhorse
-- ============================================================================
--
-- Mirrors `manyHelper-satisfy-exhaust` (DecRatParse/Properties) but
-- for the two-branch `parseStringChar` parser.  Induction on `cs + n`;
-- each step case-splits on `c ≟ᶜ '"'` and discharges the `sameLengthᵇ`
-- progress check via `sameLengthᵇ-cons` (literal) or `-cons-cons`
-- (escape).

-- Mutual-recursion structure: the `'"' ∷ cs'` clause directly recurses
-- (shrinking `cs'`); the `(c ∷ cs')` catch-all's `yes refl` branch can't
-- structurally shrink from `(c ∷ cs')` to `('"' ∷ cs')` (same list),
-- so it delegates to a named helper `-escape-step` that recurses on the
-- strictly smaller tail.

private
  manyHelper-parseStringChar-exhaust-escape-step :
    ∀ (pos : Position) (cs' : List Char) (suffix : List Char) (n' : ℕ)
    → SuffixStops (λ c → c ≈ᵇ '"') suffix
    → length cs' ≤ n'
    → proj₂ (manyHelper parseStringChar pos
               ('"' ∷ '"' ∷ escape-body-chars cs' ++ₗ '"' ∷ suffix) (suc n'))
      ≡ just (mkResult ('"' ∷ cs')
               (advancePositions pos
                  ('"' ∷ '"' ∷ escape-body-chars cs'))
               ('"' ∷ suffix))

manyHelper-parseStringChar-exhaust :
  ∀ (pos : Position) (cs : List Char) (suffix : List Char) (n : ℕ)
  → SuffixStops (λ c → c ≈ᵇ '"') suffix
  → length cs ≤ n
  → proj₂ (manyHelper parseStringChar pos
             (escape-body-chars cs ++ₗ '"' ∷ suffix) n)
    ≡ just (mkResult cs
             (advancePositions pos (escape-body-chars cs))
             ('"' ∷ suffix))
manyHelper-parseStringChar-exhaust pos [] suffix zero     _  _         = refl
manyHelper-parseStringChar-exhaust pos [] suffix (suc n') ss _
  with parseStringChar pos ('"' ∷ suffix)
     | parseStringChar-fail-at-close pos suffix ss
... | w , nothing | refl = refl
manyHelper-parseStringChar-exhaust pos ('"' ∷ cs') suffix (suc n') ss (s≤s len≤) =
  manyHelper-parseStringChar-exhaust-escape-step pos cs' suffix n' ss len≤
manyHelper-parseStringChar-exhaust pos (c ∷ cs') suffix (suc n') ss (s≤s len≤)
  with c ≟ᶜ '"'
... | yes refl =
      manyHelper-parseStringChar-exhaust-escape-step pos cs' suffix n' ss len≤
... | no c≢quote
  with parseStringChar pos (c ∷ escape-body-chars cs' ++ₗ '"' ∷ suffix)
     | parseStringChar-literal pos c
         (escape-body-chars cs' ++ₗ '"' ∷ suffix) c≢quote
...   | w , just r | refl
  rewrite sameLengthᵇ-cons c (escape-body-chars cs' ++ₗ '"' ∷ suffix)
  with manyHelper parseStringChar (advancePosition pos c)
         (escape-body-chars cs' ++ₗ '"' ∷ suffix) n'
     | manyHelper-parseStringChar-exhaust
         (advancePosition pos c) cs' suffix n' ss len≤
...     | w' , just r' | refl = refl

manyHelper-parseStringChar-exhaust-escape-step pos cs' suffix n' ss len≤
  rewrite sameLengthᵇ-cons-cons '"' '"' (escape-body-chars cs' ++ₗ '"' ∷ suffix)
  with manyHelper parseStringChar
         (advancePosition (advancePosition pos '"') '"')
         (escape-body-chars cs' ++ₗ '"' ∷ suffix) n'
     | manyHelper-parseStringChar-exhaust
         (advancePosition (advancePosition pos '"') '"') cs' suffix n' ss len≤
... | w' , just r' | refl = refl

-- ============================================================================
-- parseStringLit roundtrip
-- ============================================================================
--
-- Compose: opening `"` via `char-matches`, body via
-- `manyHelper-parseStringChar-exhaust` specialised at `length input`
-- fuel, closing `"` via `char-matches`, final `pure cs`
-- (`parseStringLit : Parser (List Char)` returns the body
-- chars directly — no `fromList`, no `fromList∘toList` axiom).

-- Length bound: each char in `cs` contributes ≥ 1 char to
-- `escape-body-chars cs`.  Induction on `cs`; the mutual-recursion
-- trick sidesteps the overlapping `'"' ∷ cs'` / `(c ∷ cs')` clauses.
private
  length-cs-≤-escape-body : ∀ (cs : List Char)
    → length cs ≤ length (escape-body-chars cs)

  length-cs-≤-escape-body-escape-step : ∀ (cs : List Char)
    → suc (length cs) ≤ suc (suc (length (escape-body-chars cs)))
  length-cs-≤-escape-body-escape-step cs =
    m≤n⇒m≤1+n (s≤s (length-cs-≤-escape-body cs))

  length-cs-≤-escape-body [] = z≤n
  length-cs-≤-escape-body ('"' ∷ cs) =
    length-cs-≤-escape-body-escape-step cs
  length-cs-≤-escape-body (c ∷ cs) with c ≟ᶜ '"'
  ... | yes refl = length-cs-≤-escape-body-escape-step cs
  ... | no c≢quote = s≤s (length-cs-≤-escape-body cs)

-- ============================================================================
-- parseStringLit roundtrip — composition
-- ============================================================================

parseStringLit-roundtrip : ∀ (pos : Position) (cs : List Char) (suffix : List Char)
  → SuffixStops (λ c → c ≈ᵇ '"') suffix
  → proj₂ (parseStringLit pos (quoteStringLit-chars cs ++ₗ suffix))
    ≡ just (mkResult cs
             (advancePositions pos (quoteStringLit-chars cs)) suffix)
parseStringLit-roundtrip pos cs suffix ss =
  trans (cong (λ input → proj₂ (parseStringLit pos (input ++ₗ suffix)))
              (quoteStringLit-chars-shape cs))
    (trans input-shape-adjust
      (trans step-open-quote
        (trans step-many
          (trans step-close-quote step-pure))))
  where
    body-chars : List Char
    body-chars = escape-body-chars cs

    rest-after-open : List Char
    rest-after-open = body-chars ++ₗ '"' ∷ suffix

    pos1 : Position
    pos1 = advancePosition pos '"'

    pos2 : Position
    pos2 = advancePositions pos1 body-chars

    pos3 : Position
    pos3 = advancePosition pos2 '"'

    -- After the shape-rewrite, `(quoteStringLit-chars cs) ++ₗ suffix`
    -- needs one `++ₗ-assoc` to fold the nested append into the form
    -- `'"' ∷ body-chars ++ₗ '"' ∷ suffix`.
    input-shape-adjust :
      proj₂ (parseStringLit pos
               (('"' ∷ body-chars ++ₗ '"' ∷ []) ++ₗ suffix))
      ≡ proj₂ (parseStringLit pos ('"' ∷ body-chars ++ₗ '"' ∷ suffix))
    input-shape-adjust =
      cong (λ xs → proj₂ (parseStringLit pos ('"' ∷ xs)))
           (++ₗ-assoc body-chars ('"' ∷ []) suffix)

    step-open-quote :
      proj₂ (parseStringLit pos ('"' ∷ body-chars ++ₗ '"' ∷ suffix))
      ≡ proj₂ ((many parseStringChar >>= λ chars →
                  char '"' >>= λ _ → pure chars)
                 pos1 rest-after-open)
    step-open-quote =
      bind-just-step (char '"')
        (λ _ → many parseStringChar >>= λ chars →
               char '"' >>= λ _ → pure chars)
        pos ('"' ∷ rest-after-open)
        '"' pos1 rest-after-open
        (char-matches '"' pos rest-after-open)

    many-success :
      proj₂ (many parseStringChar pos1 rest-after-open)
      ≡ just (mkResult cs pos2 ('"' ∷ suffix))
    many-success =
      manyHelper-parseStringChar-exhaust pos1 cs suffix
        (length rest-after-open) ss len-bound
      where
        open import Data.List.Properties
          using () renaming (length-++ to length-++ₗ-prop)

        len-bound : length cs ≤ length rest-after-open
        len-bound =
          ≤-trans (length-cs-≤-escape-body cs)
            (subst (λ n → length body-chars ≤ n)
                   (sym (length-++ₗ-prop body-chars {'"' ∷ suffix}))
                   (m≤m+n (length body-chars) (length ('"' ∷ suffix))))

    step-many :
      proj₂ ((many parseStringChar >>= λ chars →
                char '"' >>= λ _ → pure chars)
               pos1 rest-after-open)
      ≡ proj₂ ((char '"' >>= λ _ → pure cs)
                 pos2 ('"' ∷ suffix))
    step-many =
      bind-just-step (many parseStringChar)
        (λ chars → char '"' >>= λ _ → pure chars)
        pos1 rest-after-open
        cs pos2 ('"' ∷ suffix)
        many-success

    step-close-quote :
      proj₂ ((char '"' >>= λ _ → pure cs)
               pos2 ('"' ∷ suffix))
      ≡ proj₂ (pure cs pos3 suffix)
    step-close-quote =
      bind-just-step (char '"')
        (λ _ → pure cs)
        pos2 ('"' ∷ suffix)
        '"' pos3 suffix
        (char-matches '"' pos2 suffix)

    step-pure :
      proj₂ (pure cs pos3 suffix)
      ≡ just (mkResult cs
               (advancePositions pos (quoteStringLit-chars cs))
               suffix)
    step-pure = cong (λ p → just (mkResult cs p suffix)) pos3-eq
      where
        -- `pos3 ≡ advancePositions pos (quoteStringLit-chars cs)` by
        -- walking the shape.  `advancePositions` over a cons: advance
        -- one char, then recurse; over `++ₗ`, `advancePositions pos
        -- (xs ++ ys) ≡ advancePositions (advancePositions pos xs) ys`.
        pos3-eq : pos3
          ≡ advancePositions pos (quoteStringLit-chars cs)
        pos3-eq =
          trans (sym (advancePositions-++
                        (advancePositions pos1 body-chars)
                        ('"' ∷ []) []))
            (trans (sym (advancePositions-++ pos1 body-chars ('"' ∷ [])))
              (cong (advancePositions pos)
                    (sym (quoteStringLit-chars-shape cs))))


-- ============================================================================
-- Tier B — mux marker roundtrip (extracted)
-- ============================================================================
--
-- The four
-- `parseMuxMarker-*` roundtrips moved to
-- `Properties.Primitives.MuxMarker` to bring this module under the
-- 800-LOC trigger.  The submodule imports `alt-left-just`,
-- `alt-right-nothing`, `bind-nothing`, and `parseWS-one-space` from
-- this base module — `MuxMarker → Primitives` is the only allowed
-- direction.  Re-export to consumers happens in
-- `Aletheia.DBC.TextParser.Properties` (the existing primitive facade);
-- adding a `public` re-export here would close a cycle.
