{-# OPTIONS --safe --without-K #-}

-- `parseReceiverList-roundtrip` + `stripVectorPlaceholder` lemmas
-- (B.3.d Layer 3 Commit 3d.2).
--
-- Bind chain (matches `Aletheia.DBC.TextParser.Topology.parseReceiverList`):
--
--   parseIdentifier >>= λ h →
--   many (char ',' *> parseIdentifier) >>= λ t →
--   pure (h ∷ t)
--
-- Two emit shapes from `TextFormatter.Topology.emitReceivers-chars`:
--   * `[]`        → `"Vector__XXX"` placeholder (cantools convention; the
--                   grammar requires ≥1 receiver, so the empty in-memory
--                   list emits this single drop-field name).
--   * `r ∷ rs`    → `name r` followed by `,name x` for each `x ∈ rs`.
--
-- Plus the parser-side post-processing `stripVectorPlaceholder`, which
-- collapses a singleton `[Vector__XXX]` back to `[]` in the cons branch
-- of the parser's outer `pure`.  The roundtrip closes through the
-- composition `stripVectorPlaceholder ∘ <result of parseReceiverList>`.
--
-- Four sub-lemmas (advisor's split):
--   1. `parseReceiverList-roundtrip-empty`   — placeholder case:
--      parses to `[ident-VectorXXX]`.
--   2. `parseReceiverList-roundtrip-cons`    — non-empty case:
--      parses to the input list verbatim.
--   3. `stripVectorPlaceholder-vectorXXX`    — `strip [VectorXXX] ≡ []`.
--   4. `stripVectorPlaceholder-no-vectorXXX` — `strip` is identity on
--      VectorXXX-free lists.
--
-- Composed theorem `parseReceiverList∘strip-roundtrip` exposed for 3d.3.
--
-- Per-receiver precondition: NONE.  `validIdentifierᵇ (toList (name r))`
-- is built into the `Identifier` record; that's all parseIdentifier-
-- roundtrip needs.  The `,`-separator is a single literal char, so no
-- per-name char-class disjointness witness is owed.
--
-- Suffix precondition: `SuffixStops isReceiverCont suffix`, where
-- `isReceiverCont c = isIdentCont c ∨ (c ≈ᵇ ',')`.  Captures BOTH the
-- inner-many's stop condition (parseIdentifier's inner `many (satisfy
-- isIdentCont)`) AND the outer-many's stop condition (the `char ','`
-- separator).  Caller (parseSignalLine in 3d.3) discharges this from
-- the fact that what follows receivers is `parseWSOpt *> parseNewline`,
-- whose head is hspace or LF — both have `isReceiverCont ≡ false`.
module Aletheia.DBC.TextParser.Properties.Topology.Receivers where

open import Data.Bool using (Bool; true; false; T; _∨_; _∧_)
open import Data.Char using (Char; _≈ᵇ_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; length; foldr) renaming (_++_ to _++ₗ_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Properties using () renaming (length-++ to length-++ₗ; ++-assoc to ++ₗ-assoc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; ≤-refl; n≤1+n; m≤m+n; m≤n+m)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Char using () renaming (_≟_ to _≟ᶜ_)
open import Data.List.Properties as ListProps using ()
open import Data.String using (toList)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_; yes; no)

open import Aletheia.Parser.Combinators using
  (Parser; Position; ParseResult; mkResult; advancePosition; advancePositions;
   sameLengthᵇ; pure; _>>=_; _*>_; char; satisfy; many; manyHelper)
open import Aletheia.DBC.Identifier using
  (Identifier; mkIdent; isIdentStart; isIdentCont; validIdentifierᵇ)
open import Aletheia.DBC.TextParser.Lexer using (parseIdentifier)
open import Aletheia.DBC.TextParser.Topology using
  (parseReceiverList; stripVectorPlaceholder)
open import Aletheia.DBC.TextFormatter.Topology using (emitReceivers-chars)
open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; []-stop; ∷-stop; bind-just-step; advancePositions-++)
open import Aletheia.DBC.TextParser.Properties.Primitives using
  (parseIdentifier-roundtrip)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (manyHelper-prog-cons)

-- Load-bearing canary — ensures `validIdentifierᵇ (toList "Vector__XXX")`
-- reduces to `true` on the closed-Char path (so `mkIdent "Vector__XXX" tt`
-- typechecks).  Same canary EnvVar.agda imports.
import Aletheia.DBC.TextParser.Properties.EnvVars._Scratch

-- ============================================================================
-- LOCAL: ident-VectorXXX
-- ============================================================================

-- The placeholder identifier the formatter emits (`emitReceivers-chars
-- [] = toList "Vector__XXX"`) and the parser recovers.  Defined locally
-- — duplicated from `EnvVars/EnvVar.agda:120`, but importing across
-- packages would reverse the natural Topology → EnvVars dependency
-- direction.  `validIdentifierᵇ (toList "Vector__XXX")` reduces to
-- `true` on the closed-Char path (canary above).
ident-VectorXXX : Identifier
ident-VectorXXX = mkIdent (toList "Vector__XXX") tt

-- The placeholder's name string (definitional; useful as a refl in the
-- strip lemma).  Post-3d.4: `Identifier.name : List Char`, so the LHS
-- is `toList "Vector__XXX"` literal directly.
ident-VectorXXX-name : Identifier.name ident-VectorXXX ≡ toList "Vector__XXX"
ident-VectorXXX-name = refl


-- ============================================================================
-- CHARACTER PREDICATE: isReceiverCont
-- ============================================================================

-- `isIdentCont` extended with `c ≈ᵇ ','` — captures BOTH the inner-many
-- stop condition (`many (satisfy isIdentCont)` inside parseIdentifier)
-- AND the outer-many stop condition (`char ','` separator at the start
-- of each iteration).  A single `SuffixStops isReceiverCont suffix`
-- precondition discharges both.
isReceiverCont : Char → Bool
isReceiverCont c = isIdentCont c ∨ (c ≈ᵇ ',')

private
  ∨-elim-false : ∀ {b₁ b₂ : Bool} → b₁ ∨ b₂ ≡ false
                                → (b₁ ≡ false) × (b₂ ≡ false)
  ∨-elim-false {false} {false} _  = refl , refl
  ∨-elim-false {true}  {_}     ()
  ∨-elim-false {false} {true}  ()

isReceiverCont-false-isIdentCont : ∀ (c : Char)
  → isReceiverCont c ≡ false → isIdentCont c ≡ false
isReceiverCont-false-isIdentCont c eq =
  proj₁ (∨-elim-false {isIdentCont c} {c ≈ᵇ ','} eq)

isReceiverCont-false-comma : ∀ (c : Char)
  → isReceiverCont c ≡ false → (c ≈ᵇ ',') ≡ false
isReceiverCont-false-comma c eq =
  proj₂ (∨-elim-false {isIdentCont c} {c ≈ᵇ ','} eq)

isReceiverCont-stop→isIdentCont-stop :
    ∀ (suffix : List Char)
  → SuffixStops isReceiverCont suffix
  → SuffixStops isIdentCont suffix
isReceiverCont-stop→isIdentCont-stop []      _          = []-stop
isReceiverCont-stop→isIdentCont-stop (c ∷ _) (∷-stop h) =
  ∷-stop (isReceiverCont-false-isIdentCont c h)


-- ============================================================================
-- BODY DECOMPOSITION: commaSep-chars
-- ============================================================================

-- The body of `parseReceiverList` after the head identifier — one
-- `,name` group per remaining receiver.  Pulling this out keeps the
-- inductive proof on `rs` clean: the head is parsed by `parseIdentifier`,
-- and the inner `many` consumes exactly `commaSep-chars rs`.
commaSep-chars : List Identifier → List Char
commaSep-chars []       = []
commaSep-chars (r ∷ rs) =
  ',' ∷ Identifier.name r ++ₗ commaSep-chars rs

-- Reshape `emitReceivers-chars (r ∷ rs)` to bind-chain-friendly form.
private
  emitReceivers-chars-foldr-shape : ∀ (rs : List Identifier)
    → foldr (λ x acc → ',' ∷ Identifier.name x ++ₗ acc) [] rs
      ≡ commaSep-chars rs
  emitReceivers-chars-foldr-shape []       = refl
  emitReceivers-chars-foldr-shape (r ∷ rs) =
    cong (',' ∷_)
      (cong (Identifier.name r ++ₗ_)
            (emitReceivers-chars-foldr-shape rs))

emitReceivers-chars-cons-shape : ∀ (r : Identifier) (rs : List Identifier)
  → emitReceivers-chars (r ∷ rs)
    ≡ Identifier.name r ++ₗ commaSep-chars rs
emitReceivers-chars-cons-shape r rs =
  cong (Identifier.name r ++ₗ_)
       (emitReceivers-chars-foldr-shape rs)


-- ============================================================================
-- POSITION TRACKING: afterReceivers
-- ============================================================================

afterReceivers : Position → List Identifier → Position
afterReceivers pos []       = pos
afterReceivers pos (r ∷ rs) =
  afterReceivers
    (advancePositions
       (advancePosition pos ',')
       (Identifier.name r)) rs

private
  afterReceivers-advancePositions : ∀ (pos : Position) (rs : List Identifier)
    → afterReceivers pos rs ≡ advancePositions pos (commaSep-chars rs)
  afterReceivers-advancePositions pos []       = refl
  afterReceivers-advancePositions pos (r ∷ rs) =
    trans (afterReceivers-advancePositions
             (advancePositions (advancePosition pos ',')
                               (Identifier.name r))
             rs)
      (sym (advancePositions-++
              (advancePosition pos ',')
              (Identifier.name r)
              (commaSep-chars rs)))


-- ============================================================================
-- TERMINATION: many fails on receiver-stop suffix
-- ============================================================================

private
  -- Generic: `(p >>= f) pos input ≡ nothing` whenever `p pos input ≡
  -- nothing`.  Mirrors `bind-just-step`'s with-localisation pattern —
  -- abstracts `with p pos input | eq` at a fresh variable so the goal's
  -- `_>>=_` reduction lands on a `nothing` branch directly.
  bind-fail-step : ∀ {A B : Set} (p : Parser A) (f : A → Parser B)
    (pos : Position) (input : List Char)
    → p pos input ≡ nothing
    → (p >>= f) pos input ≡ nothing
  bind-fail-step p f pos input eq with p pos input | eq
  ... | nothing | refl = refl

  -- `satisfy pred pos (c ∷ cs) ≡ nothing` whenever `pred c ≡ false`.
  -- Generic in the predicate (so `rewrite eq` substitutes only the
  -- `pred c` token in the goal — never the underlying `_≈ᵇ_` /
  -- `Data.Nat._≡ᵇ_` reduction that `_*>_` exposes for `char ','`).
  satisfy-fail-cons : ∀ (pred : Char → Bool) (pos : Position)
                       (c : Char) (cs : List Char)
    → pred c ≡ false
    → satisfy pred pos (c ∷ cs) ≡ nothing
  satisfy-fail-cons pred pos c cs eq rewrite eq = refl

  -- `char ','` fails on `c ∷ cs` when `(c ≈ᵇ ',') ≡ false`.
  char-comma-fail-on-non-comma : ∀ (pos : Position) (c : Char) (cs : List Char)
    → (c ≈ᵇ ',') ≡ false
    → char ',' pos (c ∷ cs) ≡ nothing
  char-comma-fail-on-non-comma pos c cs eq =
    satisfy-fail-cons (λ c' → c' ≈ᵇ ',') pos c cs eq

  -- `char ','` fails on `[]` directly.
  char-comma-fail-on-empty : ∀ (pos : Position)
    → char ',' pos [] ≡ nothing
  char-comma-fail-on-empty _ = refl

  -- `(char ',' *> parseIdentifier)` fails on a receiver-stop suffix —
  -- empty input fails `char ','` directly, non-empty input fails via
  -- the `(c ≈ᵇ ',') ≡ false` half of `isReceiverCont c ≡ false`.
  comma-ident-fail-on-suffix : ∀ (pos : Position) (suffix : List Char)
    → SuffixStops isReceiverCont suffix
    → (char ',' *> parseIdentifier) pos suffix ≡ nothing
  comma-ident-fail-on-suffix pos []        _          =
    bind-fail-step (char ',') (λ _ → parseIdentifier) pos []
      (char-comma-fail-on-empty pos)
  comma-ident-fail-on-suffix pos (c ∷ cs) (∷-stop h) =
    bind-fail-step (char ',') (λ _ → parseIdentifier) pos (c ∷ cs)
      (char-comma-fail-on-non-comma pos c cs (isReceiverCont-false-comma c h))

-- manyHelper terminates on receiver-stop suffix at any fuel.
manyHelper-comma-ident-stop :
    ∀ (pos : Position) (suffix : List Char) (m : ℕ)
  → SuffixStops isReceiverCont suffix
  → manyHelper (char ',' *> parseIdentifier) pos suffix m
    ≡ just (mkResult [] pos suffix)
manyHelper-comma-ident-stop _   _      zero    _  = refl
manyHelper-comma-ident-stop pos suffix (suc _) ss
  rewrite comma-ident-fail-on-suffix pos suffix ss = refl


-- ============================================================================
-- SINGLE ITERATION: comma-ident-step
-- ============================================================================

-- After a `,` separator, the next iteration is parseIdentifier on the
-- name body.  `char ','` succeeds by `refl` (`',' ≈ᵇ ','` reduces to
-- `true` on closed Chars).  parseIdentifier closes via the existing
-- Layer-2 roundtrip primitive.
private
  char-comma-success-cons : ∀ (pos : Position) (rest : List Char)
    → char ',' pos (',' ∷ rest)
      ≡ just (mkResult ',' (advancePosition pos ',') rest)
  char-comma-success-cons _ _ = refl

comma-ident-step :
    ∀ (pos : Position) (r : Identifier) (rest : List Char)
  → SuffixStops isIdentCont rest
  → (char ',' *> parseIdentifier) pos
      (',' ∷ Identifier.name r ++ₗ rest)
    ≡ just (mkResult r
            (advancePositions
               (advancePosition pos ',')
               (Identifier.name r))
            rest)
comma-ident-step pos r rest ident-ss =
  trans
    (bind-just-step (char ',') (λ _ → parseIdentifier)
       pos (',' ∷ Identifier.name r ++ₗ rest)
       ',' (advancePosition pos ',')
       (Identifier.name r ++ₗ rest)
       (char-comma-success-cons pos
          (Identifier.name r ++ₗ rest)))
    (parseIdentifier-roundtrip
       (advancePosition pos ',')
       r rest ident-ss)


-- ============================================================================
-- INDUCTIVE: manyHelper-comma-ident-body
-- ============================================================================

-- After consuming `commaSep-chars rs`, the manyHelper returns `rs` and
-- leaves `suffix` unconsumed (with the cursor at `afterReceivers pos
-- rs`).  Mirrors Nodes.agda's `manyHelper-parseWSIdent-body` but with
-- `,` separator instead of leading whitespace.
private
  -- Generic: `length ys < length xs → sameLengthᵇ xs ys ≡ false`.
  -- Duplicated from Nodes.agda (private there); lift to a shared
  -- location when more Layer-3 constructs need it.
  sameLengthᵇ-lt : ∀ {A : Set} (xs ys : List A)
    → length ys < length xs
    → sameLengthᵇ xs ys ≡ false
  sameLengthᵇ-lt []       []       ()
  sameLengthᵇ-lt []       (_ ∷ _)  ()
  sameLengthᵇ-lt (_ ∷ _)  []       _       = refl
  sameLengthᵇ-lt (_ ∷ xs) (_ ∷ ys) (s≤s h) = sameLengthᵇ-lt xs ys h

  -- Per-iteration progress witness — `',' ∷ name r ++ rest` is strictly
  -- longer than `rest` (it has at least one extra char).
  sameLengthᵇ-comma-iter-fail : ∀ (r : Identifier) (rest : List Char)
    → sameLengthᵇ (',' ∷ Identifier.name r ++ₗ rest) rest
      ≡ false
  sameLengthᵇ-comma-iter-fail r rest =
    sameLengthᵇ-lt
      (',' ∷ Identifier.name r ++ₗ rest) rest len-witness
    where
      len-witness :
        length rest < length (',' ∷ Identifier.name r ++ₗ rest)
      len-witness
        rewrite length-++ₗ (Identifier.name r) {rest} =
          s≤s (m≤n+m (length rest) (length (Identifier.name r)))

  -- The post-many-body input is `commaSep-chars rs ++ suffix`.  Its
  -- head is either `,` (next iter) or the head of suffix
  -- (`isReceiverCont` false → `isIdentCont` false).  Both have
  -- `isIdentCont c ≡ false`.
  commaSep-isIdentCont-stop :
      ∀ (rs : List Identifier) (suffix : List Char)
    → SuffixStops isReceiverCont suffix
    → SuffixStops isIdentCont (commaSep-chars rs ++ₗ suffix)
  commaSep-isIdentCont-stop []        suffix ss =
    isReceiverCont-stop→isIdentCont-stop suffix ss
  commaSep-isIdentCont-stop (_ ∷ _)   _      _  = ∷-stop refl

manyHelper-comma-ident-body :
    ∀ (pos : Position) (rs : List Identifier) (suffix : List Char) (m : ℕ)
  → SuffixStops isReceiverCont suffix
  → length rs ≤ m
  → manyHelper (char ',' *> parseIdentifier) pos
      (commaSep-chars rs ++ₗ suffix) m
    ≡ just (mkResult rs (afterReceivers pos rs) suffix)
manyHelper-comma-ident-body pos []       suffix m       ss _ =
  manyHelper-comma-ident-stop pos suffix m ss
manyHelper-comma-ident-body pos (r ∷ rs) suffix (suc m')
    ss (s≤s len-le) =
  let
    iter-rest : List Char
    iter-rest = commaSep-chars rs ++ₗ suffix

    pos-after-comma : Position
    pos-after-comma = advancePosition pos ','

    pos-after-name : Position
    pos-after-name =
      advancePositions pos-after-comma (Identifier.name r)

    iter-rest-ss : SuffixStops isIdentCont iter-rest
    iter-rest-ss = commaSep-isIdentCont-stop rs suffix ss

    iter-eq :
      (char ',' *> parseIdentifier) pos
        (',' ∷ Identifier.name r ++ₗ iter-rest)
      ≡ just (mkResult r pos-after-name iter-rest)
    iter-eq = comma-ident-step pos r iter-rest iter-rest-ss

    rec-eq :
      manyHelper (char ',' *> parseIdentifier) pos-after-name iter-rest m'
      ≡ just (mkResult rs (afterReceivers pos-after-name rs) suffix)
    rec-eq =
      manyHelper-comma-ident-body pos-after-name rs suffix m' ss len-le

    -- Reshape `(',' ∷ name ++ commaSep rs) ++ suffix
    -- ≡ ',' ∷ name ++ (commaSep rs ++ suffix)`.
    shape-eq :
      commaSep-chars (r ∷ rs) ++ₗ suffix
      ≡ ',' ∷ Identifier.name r ++ₗ iter-rest
    shape-eq =
      cong (',' ∷_)
        (++ₗ-assoc (Identifier.name r)
                   (commaSep-chars rs)
                   suffix)
  in
    trans
      (cong (λ input →
               manyHelper (char ',' *> parseIdentifier) pos input (suc m'))
            shape-eq)
      (manyHelper-prog-cons (char ',' *> parseIdentifier) pos
        (',' ∷ Identifier.name r ++ₗ iter-rest) m'
        r pos-after-name iter-rest
        rs
        (afterReceivers pos-after-name rs)
        suffix
        iter-eq
        (sameLengthᵇ-comma-iter-fail r iter-rest)
        rec-eq)


-- ============================================================================
-- LEMMA 1: parseReceiverList-roundtrip-empty
-- ============================================================================

-- Empty input → "Vector__XXX" placeholder → parser recovers
-- `[ident-VectorXXX]`.
parseReceiverList-roundtrip-empty :
    ∀ (pos : Position) (suffix : List Char)
  → SuffixStops isReceiverCont suffix
  → parseReceiverList pos (emitReceivers-chars [] ++ₗ suffix)
    ≡ just (mkResult (ident-VectorXXX ∷ [])
            (advancePositions pos (emitReceivers-chars []))
            suffix)
parseReceiverList-roundtrip-empty pos suffix ss =
  trans step-parseIdentifier (trans step-many step-pure)
  where
    pos-after-name : Position
    pos-after-name = advancePositions pos (toList "Vector__XXX")

    cont-after-ident : Identifier → Parser (List Identifier)
    cont-after-ident h =
      many (char ',' *> parseIdentifier) >>= λ t →
      pure (h ∷ t)

    cont-after-many : List Identifier → Parser (List Identifier)
    cont-after-many t = pure (ident-VectorXXX ∷ t)

    step-parseIdentifier :
      parseReceiverList pos (toList "Vector__XXX" ++ₗ suffix)
      ≡ cont-after-ident ident-VectorXXX pos-after-name suffix
    step-parseIdentifier =
      bind-just-step parseIdentifier cont-after-ident
        pos (toList "Vector__XXX" ++ₗ suffix)
        ident-VectorXXX pos-after-name suffix
        (parseIdentifier-roundtrip pos ident-VectorXXX suffix
          (isReceiverCont-stop→isIdentCont-stop suffix ss))

    step-many :
      cont-after-ident ident-VectorXXX pos-after-name suffix
      ≡ pure (ident-VectorXXX ∷ []) pos-after-name suffix
    step-many =
      bind-just-step (many (char ',' *> parseIdentifier)) cont-after-many
        pos-after-name suffix
        [] pos-after-name suffix
        (manyHelper-comma-ident-stop pos-after-name suffix (length suffix) ss)

    step-pure :
      pure (ident-VectorXXX ∷ []) pos-after-name suffix
      ≡ just (mkResult (ident-VectorXXX ∷ [])
              (advancePositions pos (emitReceivers-chars []))
              suffix)
    step-pure = refl


-- ============================================================================
-- LEMMA 2: parseReceiverList-roundtrip-cons
-- ============================================================================

-- Non-empty input → `name r ++ commaSep-chars rs` → parser recovers
-- `r ∷ rs` verbatim.
parseReceiverList-roundtrip-cons :
    ∀ (pos : Position) (r : Identifier) (rs : List Identifier)
      (suffix : List Char)
  → SuffixStops isReceiverCont suffix
  → parseReceiverList pos (emitReceivers-chars (r ∷ rs) ++ₗ suffix)
    ≡ just (mkResult (r ∷ rs)
            (advancePositions pos (emitReceivers-chars (r ∷ rs)))
            suffix)
parseReceiverList-roundtrip-cons pos r rs suffix ss =
  trans
    (cong (λ input → parseReceiverList pos input)
          (trans
            (cong (_++ₗ suffix) (emitReceivers-chars-cons-shape r rs))
            (++ₗ-assoc (Identifier.name r)
                       (commaSep-chars rs)
                       suffix)))
    (trans step-parseIdentifier
      (trans step-many step-pure))
  where
    pos-after-name : Position
    pos-after-name = advancePositions pos (Identifier.name r)

    pos-after-many : Position
    pos-after-many = afterReceivers pos-after-name rs

    cont-after-ident : Identifier → Parser (List Identifier)
    cont-after-ident h =
      many (char ',' *> parseIdentifier) >>= λ t →
      pure (h ∷ t)

    cont-after-many : List Identifier → Parser (List Identifier)
    cont-after-many t = pure (r ∷ t)

    parseIdent-suffix-ss : SuffixStops isIdentCont
                            (commaSep-chars rs ++ₗ suffix)
    parseIdent-suffix-ss = commaSep-isIdentCont-stop rs suffix ss

    step-parseIdentifier :
      parseReceiverList pos
        (Identifier.name r ++ₗ commaSep-chars rs ++ₗ suffix)
      ≡ cont-after-ident r pos-after-name (commaSep-chars rs ++ₗ suffix)
    step-parseIdentifier =
      bind-just-step parseIdentifier cont-after-ident
        pos (Identifier.name r ++ₗ commaSep-chars rs ++ₗ suffix)
        r pos-after-name (commaSep-chars rs ++ₗ suffix)
        (parseIdentifier-roundtrip pos r
          (commaSep-chars rs ++ₗ suffix) parseIdent-suffix-ss)

    body-fuel-bound :
      length rs ≤ length (commaSep-chars rs ++ₗ suffix)
    body-fuel-bound
      rewrite length-++ₗ (commaSep-chars rs) {suffix} =
        ≤-trans
          (length-rs-le-commaSep rs)
          (m≤m+n (length (commaSep-chars rs)) (length suffix))
      where
        length-rs-le-commaSep : ∀ (rs : List Identifier)
          → length rs ≤ length (commaSep-chars rs)
        length-rs-le-commaSep []        = z≤n
        length-rs-le-commaSep (r' ∷ rs') =
          s≤s
            (≤-trans
               (length-rs-le-commaSep rs')
               (le-monotone-++
                  (Identifier.name r')
                  (commaSep-chars rs')))
          where
            le-monotone-++ : ∀ (xs ys : List Char)
              → length ys ≤ length (xs ++ₗ ys)
            le-monotone-++ []        ys = ≤-refl
            le-monotone-++ (_ ∷ xs') ys =
              ≤-trans (le-monotone-++ xs' ys) (n≤1+n _)

    rec-call :
      manyHelper (char ',' *> parseIdentifier) pos-after-name
        (commaSep-chars rs ++ₗ suffix)
        (length (commaSep-chars rs ++ₗ suffix))
      ≡ just (mkResult rs pos-after-many suffix)
    rec-call = manyHelper-comma-ident-body
                 pos-after-name rs suffix
                 (length (commaSep-chars rs ++ₗ suffix))
                 ss body-fuel-bound

    step-many :
      cont-after-ident r pos-after-name (commaSep-chars rs ++ₗ suffix)
      ≡ pure (r ∷ rs) pos-after-many suffix
    step-many =
      bind-just-step (many (char ',' *> parseIdentifier)) cont-after-many
        pos-after-name (commaSep-chars rs ++ₗ suffix)
        rs pos-after-many suffix
        rec-call

    -- Bridge `pos-after-many ≡ advancePositions pos (emitReceivers-chars (r ∷ rs))`
    -- via afterReceivers-advancePositions + advancePositions-++ +
    -- emitReceivers-chars-cons-shape.
    pos-final-eq :
      pos-after-many ≡ advancePositions pos (emitReceivers-chars (r ∷ rs))
    pos-final-eq =
      trans
        (afterReceivers-advancePositions pos-after-name rs)
        (trans
          (sym (advancePositions-++ pos
                  (Identifier.name r)
                  (commaSep-chars rs)))
          (cong (advancePositions pos)
                (sym (emitReceivers-chars-cons-shape r rs))))

    step-pure :
      pure (r ∷ rs) pos-after-many suffix
      ≡ just (mkResult (r ∷ rs)
              (advancePositions pos (emitReceivers-chars (r ∷ rs)))
              suffix)
    step-pure = cong (λ p → just (mkResult (r ∷ rs) p suffix)) pos-final-eq


-- ============================================================================
-- LEMMA 3: stripVectorPlaceholder-vectorXXX
-- ============================================================================

-- `stripVectorPlaceholder` collapses the placeholder singleton to `[]`.
-- Closes by `refl` because the closed-string `≟` reduces to `yes`.
stripVectorPlaceholder-vectorXXX :
  stripVectorPlaceholder (ident-VectorXXX ∷ []) ≡ []
stripVectorPlaceholder-vectorXXX = refl


-- ============================================================================
-- LEMMA 4: stripVectorPlaceholder-no-vectorXXX
-- ============================================================================

-- `stripVectorPlaceholder` is the identity on lists whose elements
-- are not literally named `"Vector__XXX"`.  Three sub-cases by list
-- shape: empty (refl), singleton (with-on-≟), longer (refl by
-- catch-all clause).
stripVectorPlaceholder-no-vectorXXX :
    ∀ (rs : List Identifier)
  → All (λ r → ¬ Identifier.name r ≡ toList "Vector__XXX") rs
  → stripVectorPlaceholder rs ≡ rs
stripVectorPlaceholder-no-vectorXXX []           _              = refl
stripVectorPlaceholder-no-vectorXXX (r ∷ [])     (¬eq All.∷ All.[])
  with ListProps.≡-dec _≟ᶜ_ (Identifier.name r) (toList "Vector__XXX")
... | yes eq = ⊥-elim (¬eq eq)
... | no  _  = refl
stripVectorPlaceholder-no-vectorXXX (_ ∷ _ ∷ _)  _              = refl


-- ============================================================================
-- COMPOSED THEOREM (for 3d.3)
-- ============================================================================

-- Caller contract: given a NoVectorXXX precondition on the in-memory
-- list AND a SuffixStops on the trailing input, the parser returns
-- some `parsedRs` such that `strip parsedRs ≡ rs`.  Existential keeps
-- the parser-image opaque to 3d.3 (which only cares about the post-
-- strip recovery).
parseReceiverList∘strip-roundtrip :
    ∀ (pos : Position) (rs : List Identifier) (suffix : List Char)
  → All (λ r → ¬ Identifier.name r ≡ toList "Vector__XXX") rs
  → SuffixStops isReceiverCont suffix
  → ∃[ parsedRs ]
        (parseReceiverList pos (emitReceivers-chars rs ++ₗ suffix)
          ≡ just (mkResult parsedRs
                  (advancePositions pos (emitReceivers-chars rs))
                  suffix))
      × (stripVectorPlaceholder parsedRs ≡ rs)
parseReceiverList∘strip-roundtrip pos []        suffix _ ss =
  ident-VectorXXX ∷ [] ,
  parseReceiverList-roundtrip-empty pos suffix ss ,
  stripVectorPlaceholder-vectorXXX
parseReceiverList∘strip-roundtrip pos (r ∷ rs) suffix novecxxx ss =
  r ∷ rs ,
  parseReceiverList-roundtrip-cons pos r rs suffix ss ,
  stripVectorPlaceholder-no-vectorXXX (r ∷ rs) novecxxx
