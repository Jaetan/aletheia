{-# OPTIONS --safe --without-K #-}

-- `parseNamespace-roundtrip` — per-line-construct roundtrip for the
-- `NS_ :` preamble block (B.3.d Layer 3).
--
-- Emitter: `toList "NS_ :\n"` + 25 cantools-canonical keyword lines
-- (each `"\t<kw>\n"`) + trailing blank `"\n"`.  Parser bind chain
-- (matches `Aletheia.DBC.TextParser.Preamble.parseNamespace`):
--
--   string "NS_"         >>= λ _ →
--   parseWSOpt           >>= λ _ →  -- consumes 1 space (NS_<space>:)
--   char ':'             >>= λ _ →
--   parseNewline         >>= λ _ →  -- header line LF
--   many parseNSLine     >>= λ _ →  -- 25 keyword lines + 1 blank + stop
--   pure tt
--
-- `parseNSLine = (parseNewline *> pure tt) <|> (parseWS *>
-- parseIdentifier *> parseWSOpt *> parseNewline *> pure tt)`.  On a
-- `'\t'`-led input the first branch fails (parseNewline fails) and
-- the second succeeds; on `'\n'` the first branch succeeds directly.
--
-- Precondition: outer `suffix` must not start with hspace, `'\n'`, or
-- `'\r'` — otherwise `many parseNSLine` would over-consume into the
-- next construct.  Combined predicate `isNSLineStart`.
--
-- Proof strategy: inductive `manyHelper-parseNSLine-body` over a
-- `List String` keyword list.  At concrete call sites the two per-
-- keyword preconditions (`T (validIdentifierᵇ (toList kw))` and
-- `SuffixStops isHSpace (toList kw)`) both reduce to `tt` / `∷-stop
-- refl` since every NS_ keyword is a literal letter-led identifier.
module Aletheia.DBC.TextParser.Properties.Preamble.Namespace where

open import Data.Bool using (Bool; true; false; T; _∨_)
open import Data.Char using (Char)
open import Data.Char.Base using (_≈ᵇ_)
open import Data.List using (List; []; _∷_; length)
  renaming (_++_ to _++ₗ_)
open import Data.List.Properties using (length-++)
  renaming (++-assoc to ++ₗ-assoc)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (n≤1+n; m≤n+m; m≤m+n; ≤-trans; +-suc)
open import Data.Product using (_×_; _,_; ∃-syntax; proj₁; proj₂)
open import Data.String using (String; toList)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Aletheia.Parser.Combinators using
  (Parser; Position; ParseResult; mkResult; advancePosition; advancePositions;
   pure; _>>=_; _<|>_; _*>_; string; char; satisfy; many; manyHelper;
   sameLengthᵇ)
open import Aletheia.DBC.Identifier using
  (Identifier; mkIdent; isIdentStart; isIdentCont; validIdentifierᵇ)
open import Aletheia.DBC.TextParser.Lexer using
  (parseIdentifier; parseWS; parseWSOpt; parseNewline; isHSpace)
open import Aletheia.DBC.TextParser.Preamble using
  (parseNamespace; parseNSLine)
open import Aletheia.DBC.TextFormatter.Preamble using
  (emitNamespace-chars)
open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; []-stop; ∷-stop; bind-just-step;
   manyHelper-satisfy-exhaust-many; sameLengthᵇ-cons;
   advancePositions-++)
-- Post-3d.4 + JSON-mirror: `parseIdentifier-consumes` no longer goes
-- through `toList∘fromList`; `Identifier.name : List Char` lets the
-- consumer pass `cs` directly into `mkIdent`.
open import Aletheia.DBC.TextParser.Properties.Primitives using
  (char-matches; string-success; alt-left-just; alt-right-nothing;
   bind-nothing; parseIdentifier-roundtrip)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart; parseNewline-match-LF; parseNewline-fail-on-stop;
   manyHelper-parseNewline-exhaust; manyHelper-one-iter;
   manyHelper-prog-cons; many-parseNewline-one-LF-stop)

-- ============================================================================
-- isNSLineStart predicate
-- ============================================================================

-- Characterises where `parseNSLine` fails and hence where `many
-- parseNSLine` terminates.  A char starts an NS_ line iff it is an
-- hspace (keyword-branch start) or a newline (blank-branch start);
-- both branches fail on any other char.
isNSLineStart : Char → Bool
isNSLineStart c = isHSpace c ∨ isNewlineStart c

-- Split the ∨ predicate into hspace and newline components.  Used to
-- dispatch a `SuffixStops isNSLineStart suffix` witness to both
-- branches' individual failure lemmas.
private
  ∨-false-split : ∀ {a b : Bool}
    → (a ∨ b) ≡ false → (a ≡ false) × (b ≡ false)
  ∨-false-split {false} {false} _ = refl , refl

  isNSLineStart-suffix-splits : ∀ (suffix : List Char)
    → SuffixStops isNSLineStart suffix
    → SuffixStops isHSpace suffix × SuffixStops isNewlineStart suffix
  isNSLineStart-suffix-splits [] _ = []-stop , []-stop
  isNSLineStart-suffix-splits (c ∷ _) (∷-stop h)
    with ∨-false-split {isHSpace c} {isNewlineStart c} h
  ... | hs , nl = ∷-stop hs , ∷-stop nl

-- ============================================================================
-- sameLengthᵇ length-based false lemma + specific shape for NS_ lines
-- ============================================================================

private
  -- Generic: `length ys < length xs → sameLengthᵇ xs ys ≡ false`.
  -- Stronger than `sameLengthᵇ-cons` (covers arbitrary-length prefix).
  sameLengthᵇ-lt : ∀ {A : Set} (xs ys : List A)
    → length ys < length xs
    → sameLengthᵇ xs ys ≡ false
  sameLengthᵇ-lt []       []       ()
  sameLengthᵇ-lt []       (y ∷ _)  ()
  sameLengthᵇ-lt (_ ∷ _)  []       _       = refl
  sameLengthᵇ-lt (_ ∷ xs) (_ ∷ ys) (s≤s h) = sameLengthᵇ-lt xs ys h

  -- `length rest < length ('\t' ∷ cs ++ '\n' ∷ rest)`: diff is `2 +
  -- length cs ≥ 2`.  Chain `n ≤ suc n ≤ n + suc n` with `length-++` to
  -- assemble the witness.
  len-rest-lt-tab-kw-nl : ∀ (cs rest : List Char)
    → length rest < length ('\t' ∷ cs ++ₗ '\n' ∷ rest)
  len-rest-lt-tab-kw-nl cs rest
    rewrite length-++ cs {'\n' ∷ rest}
    = s≤s (≤-trans (n≤1+n (length rest))
                    (m≤n+m (suc (length rest)) (length cs)))

  -- Specialised `sameLengthᵇ`-false witness for the parseNSLine keyword
  -- branch's progress check.  `manyHelper`'s sameLengthᵇ-false guard
  -- requires exactly this shape.
  sameLengthᵇ-kw-iter-fail : ∀ (cs rest : List Char)
    → sameLengthᵇ ('\t' ∷ cs ++ₗ '\n' ∷ rest) rest ≡ false
  sameLengthᵇ-kw-iter-fail cs rest =
    sameLengthᵇ-lt ('\t' ∷ cs ++ₗ '\n' ∷ rest) rest
                    (len-rest-lt-tab-kw-nl cs rest)

-- ============================================================================
-- Primitive helpers: parseWS on '\t', parseIdentifier on valid chars
-- ============================================================================

-- `parseWS = some (satisfy isHSpace)`.  For a `'\t'`-led input with a
-- non-hspace continuation, `some` succeeds with singleton `['\t']`.
-- Parallels `parseWS-one-space` (Primitives.agda).
parseWS-one-tab : ∀ (pos : Position) (suffix : List Char)
  → SuffixStops isHSpace suffix
  → parseWS pos ('\t' ∷ suffix)
    ≡ just (mkResult ('\t' ∷ [])
                     (advancePosition pos '\t') suffix)
parseWS-one-tab pos suffix ss
  rewrite manyHelper-satisfy-exhaust-many isHSpace
            (advancePosition pos '\t') [] suffix All.[] ss
  = refl

-- `parseWS` fails on a non-hspace-led input.  `some (satisfy isHSpace)`
-- applied to `c ∷ cs` with `isHSpace c ≡ false`: the inner `satisfy`
-- fails, propagating `nothing` through the `<$>` / `<*>` chain.  Used
-- for the keyword-branch failure proof of `parseNSLine-fail-on-stop`.
private
  parseWS-fail-on-char : ∀ (pos : Position) (c : Char) (cs : List Char)
    → isHSpace c ≡ false
    → parseWS pos (c ∷ cs) ≡ nothing
  parseWS-fail-on-char pos c cs h rewrite h = refl

-- Existential form of parseIdentifier-roundtrip: `parseIdentifier`
-- succeeds on any `cs ++ suffix` where `cs` is a valid-identifier
-- char list and `suffix` is at an identifier-continuation stop.
-- Post-3d.4, `Identifier.name : List Char` matches `cs` directly —
-- no `fromList`, no `toList∘fromList` bridge.  The returned Identifier
-- is `mkIdent cs valid`; `Identifier.name (mkIdent cs valid) ≡ cs`
-- reduces by record-projection, so `parseIdentifier-roundtrip` closes
-- the equation in one step.
--
-- Used for the 25 NS_ keywords: each `kw` has `validIdentifierᵇ
-- (toList kw) ≡ true` by reduction, so `T (...) = ⊤` and the
-- precondition is `tt`.
parseIdentifier-consumes :
  ∀ (pos : Position) (cs : List Char) (suffix : List Char)
  → T (validIdentifierᵇ cs)
  → SuffixStops isIdentCont suffix
  → ∃[ i ] parseIdentifier pos (cs ++ₗ suffix)
           ≡ just (mkResult i (advancePositions pos cs) suffix)
parseIdentifier-consumes pos cs suffix valid ss =
  mkIdent cs valid , parseIdentifier-roundtrip pos (mkIdent cs valid) suffix ss

-- ============================================================================
-- Hspace-stop lift under validity
-- ============================================================================

-- Given a valid identifier `cs` and `SuffixStops isHSpace cs` (which
-- holds trivially on concrete keywords whose first char is a letter or
-- `_`, neither of which is hspace), lift to `SuffixStops isHSpace (cs
-- ++ xs)` for any extension `xs`.  Validity forces `cs ≡ c ∷ _` so the
-- `[]` case is absurd.
private
  valid-SuffixStops-++ : ∀ {cs : List Char} (xs : List Char)
    → T (validIdentifierᵇ cs)
    → SuffixStops isHSpace cs
    → SuffixStops isHSpace (cs ++ₗ xs)
  valid-SuffixStops-++ {[]}     _ () _
  valid-SuffixStops-++ {_ ∷ _}  _ _  (∷-stop h) = ∷-stop h

-- ============================================================================
-- parseNSLine — per-branch lemmas
-- ============================================================================

-- Blank-line branch succeeds on a `'\n'`-led input via the first
-- `<|>` branch (`parseNewline *> pure tt`).  Doesn't need an outer
-- suffix precondition — the parseNSLine `*> pure tt` just wraps the
-- parseNewline result.
parseNSLine-blank : ∀ (pos : Position) (rest : List Char)
  → parseNSLine pos ('\n' ∷ rest)
    ≡ just (mkResult tt (advancePosition pos '\n') rest)
parseNSLine-blank pos rest =
  alt-left-just (parseNewline *> pure tt)
    (parseWS *> parseIdentifier *> parseWSOpt *> parseNewline *> pure tt)
    pos ('\n' ∷ rest) _
    (bind-just-step parseNewline (λ _ → pure tt)
      pos ('\n' ∷ rest)
      '\n' (advancePosition pos '\n') rest
      (parseNewline-match-LF pos rest))

-- Helper: `parseNSLine`'s first branch fails on a `'\t'`-led input.
-- Needed to expose the `<|>` fall-through for the keyword branch.
private
  parseNSLine-blank-branch-fails-on-tab : ∀ (pos : Position) (rest : List Char)
    → (parseNewline *> pure tt) pos ('\t' ∷ rest) ≡ nothing
  parseNSLine-blank-branch-fails-on-tab pos rest =
    bind-nothing parseNewline (λ _ → pure tt) pos ('\t' ∷ rest)
      (parseNewline-fail-on-stop pos ('\t' ∷ rest) (∷-stop refl))

-- Keyword-line branch: `parseNSLine pos ('\t' ∷ cs ++ '\n' ∷ rest)`
-- succeeds via the second `<|>` branch.  Sub-bind chain (with `_*>_`
-- left-associative, the outermost bind is `_*> pure tt`, and each
-- inner compound is peeled via `bind-just-step`):
--   parseWS       (consumes '\t') →
--   parseIdentifier (consumes cs) →
--   parseWSOpt    (consumes 0 hspace; next is '\n') →
--   parseNewline  (consumes '\n') →
--   pure tt
--
-- Preconditions:
--   * `T (validIdentifierᵇ cs)` — each concrete NS_ keyword satisfies
--     this by `validIdentifierᵇ (toList "NS_DESC_") ≡ true` reduction
--     (see `_Scratch.agda`).
--   * `SuffixStops isHSpace (cs ++ '\n' ∷ rest)` — parseWS must stop
--     after consuming exactly `'\t'`.  For a valid keyword `cs` (non-
--     empty, starting with a letter or `_`), this holds because the
--     first char of the concatenation is `cs`'s first char, which is
--     not hspace.  At concrete call sites, `∷-stop refl` discharges.
parseNSLine-keyword : ∀ (pos : Position) (cs : List Char) (rest : List Char)
  → T (validIdentifierᵇ cs)
  → SuffixStops isHSpace (cs ++ₗ '\n' ∷ rest)
  → parseNSLine pos ('\t' ∷ cs ++ₗ '\n' ∷ rest)
    ≡ just (mkResult tt
             (advancePosition
                (advancePositions (advancePosition pos '\t') cs) '\n')
             rest)
parseNSLine-keyword pos cs rest valid cs-ss =
  trans (alt-right-nothing (parseNewline *> pure tt)
           (parseWS *> parseIdentifier *> parseWSOpt *>
              parseNewline *> pure tt)
           pos ('\t' ∷ cs ++ₗ '\n' ∷ rest)
           (parseNSLine-blank-branch-fails-on-tab pos (cs ++ₗ '\n' ∷ rest)))
    keyword-branch-succeeds
  where
    pos-tab : Position
    pos-tab = advancePosition pos '\t'

    pos-ident : Position
    pos-ident = advancePositions pos-tab cs

    pos-nl : Position
    pos-nl = advancePosition pos-ident '\n'

    ident-ss : SuffixStops isIdentCont ('\n' ∷ rest)
    ident-ss = ∷-stop refl

    ident-res : ∃[ i ] parseIdentifier pos-tab (cs ++ₗ '\n' ∷ rest)
                        ≡ just (mkResult i pos-ident ('\n' ∷ rest))
    ident-res = parseIdentifier-consumes pos-tab cs ('\n' ∷ rest)
                  valid ident-ss

    ident-i : Identifier
    ident-i = proj₁ ident-res

    ident-eq : parseIdentifier pos-tab (cs ++ₗ '\n' ∷ rest)
             ≡ just (mkResult ident-i pos-ident ('\n' ∷ rest))
    ident-eq = proj₂ ident-res

    wsopt-ss : SuffixStops isHSpace ('\n' ∷ rest)
    wsopt-ss = ∷-stop refl

    wsEq : parseWS pos ('\t' ∷ cs ++ₗ '\n' ∷ rest)
         ≡ just (mkResult ('\t' ∷ []) pos-tab (cs ++ₗ '\n' ∷ rest))
    wsEq = parseWS-one-tab pos (cs ++ₗ '\n' ∷ rest) cs-ss

    wsoptEq : parseWSOpt pos-ident ('\n' ∷ rest)
            ≡ just (mkResult [] pos-ident ('\n' ∷ rest))
    wsoptEq = manyHelper-satisfy-exhaust-many isHSpace pos-ident []
                ('\n' ∷ rest) All.[] wsopt-ss

    nlEq : parseNewline pos-ident ('\n' ∷ rest)
         ≡ just (mkResult '\n' pos-nl rest)
    nlEq = parseNewline-match-LF pos-ident rest

    -- Step-by-step peel of the left-associated `_*>_` chain.  Each
    -- `bind-just-step` strips one `>>=` layer; trans chains them with
    -- the next per-parser equation.
    wsIdentEq : (parseWS *> parseIdentifier) pos ('\t' ∷ cs ++ₗ '\n' ∷ rest)
              ≡ just (mkResult ident-i pos-ident ('\n' ∷ rest))
    wsIdentEq =
      trans (bind-just-step parseWS (λ _ → parseIdentifier)
               pos ('\t' ∷ cs ++ₗ '\n' ∷ rest)
               ('\t' ∷ []) pos-tab (cs ++ₗ '\n' ∷ rest) wsEq)
        ident-eq

    wsIdentWSOptEq : ((parseWS *> parseIdentifier) *> parseWSOpt)
                      pos ('\t' ∷ cs ++ₗ '\n' ∷ rest)
                  ≡ just (mkResult [] pos-ident ('\n' ∷ rest))
    wsIdentWSOptEq =
      trans (bind-just-step (parseWS *> parseIdentifier) (λ _ → parseWSOpt)
               pos ('\t' ∷ cs ++ₗ '\n' ∷ rest)
               ident-i pos-ident ('\n' ∷ rest) wsIdentEq)
        wsoptEq

    wsIdentWSOptNLEq :
      (((parseWS *> parseIdentifier) *> parseWSOpt) *> parseNewline)
        pos ('\t' ∷ cs ++ₗ '\n' ∷ rest)
      ≡ just (mkResult '\n' pos-nl rest)
    wsIdentWSOptNLEq =
      trans (bind-just-step ((parseWS *> parseIdentifier) *> parseWSOpt)
               (λ _ → parseNewline)
               pos ('\t' ∷ cs ++ₗ '\n' ∷ rest)
               [] pos-ident ('\n' ∷ rest) wsIdentWSOptEq)
        nlEq

    keyword-branch-succeeds :
      (parseWS *> parseIdentifier *> parseWSOpt *>
         parseNewline *> pure tt)
        pos ('\t' ∷ cs ++ₗ '\n' ∷ rest)
      ≡ just (mkResult tt pos-nl rest)
    keyword-branch-succeeds =
      bind-just-step (((parseWS *> parseIdentifier) *> parseWSOpt) *>
                        parseNewline)
                     (λ _ → pure tt)
                     pos ('\t' ∷ cs ++ₗ '\n' ∷ rest)
                     '\n' pos-nl rest wsIdentWSOptNLEq

-- ============================================================================
-- parseNSLine fails on non-NS-line-start input; manyHelper exhausts
-- ============================================================================

-- `parseNSLine` fails on input whose first char is neither hspace nor
-- a newline.  Used to terminate `many parseNSLine` at the outer suffix.
parseNSLine-fail-on-stop : ∀ (pos : Position) (suffix : List Char)
  → SuffixStops isNSLineStart suffix
  → parseNSLine pos suffix ≡ nothing
parseNSLine-fail-on-stop pos [] _ = refl
parseNSLine-fail-on-stop pos (c ∷ cs) (∷-stop h)
  with ∨-false-split {isHSpace c} {isNewlineStart c} h
... | hs-false , nl-false =
    trans (alt-right-nothing (parseNewline *> pure tt)
             (parseWS *> parseIdentifier *> parseWSOpt *>
                parseNewline *> pure tt)
             pos (c ∷ cs)
             left-branch-fail)
          right-branch-fail
  where
    left-branch-fail : (parseNewline *> pure tt) pos (c ∷ cs) ≡ nothing
    left-branch-fail =
      bind-nothing parseNewline (λ _ → pure tt) pos (c ∷ cs)
        (parseNewline-fail-on-stop pos (c ∷ cs) (∷-stop nl-false))

    ws-fail : parseWS pos (c ∷ cs) ≡ nothing
    ws-fail = parseWS-fail-on-char pos c cs hs-false

    -- Build the right-branch failure from inside out: parseWS fails,
    -- so each outer `*>` bind propagates `nothing` via `bind-nothing`.
    right-branch-fail :
      (parseWS *> parseIdentifier *> parseWSOpt *>
         parseNewline *> pure tt) pos (c ∷ cs) ≡ nothing
    right-branch-fail =
      bind-nothing (((parseWS *> parseIdentifier) *> parseWSOpt) *>
                      parseNewline)
                   (λ _ → pure tt)
                   pos (c ∷ cs)
        (bind-nothing ((parseWS *> parseIdentifier) *> parseWSOpt)
          (λ _ → parseNewline)
          pos (c ∷ cs)
          (bind-nothing (parseWS *> parseIdentifier)
            (λ _ → parseWSOpt)
            pos (c ∷ cs)
            (bind-nothing parseWS (λ _ → parseIdentifier)
              pos (c ∷ cs) ws-fail)))

-- `manyHelper parseNSLine` terminates as the empty list on any fuel
-- when the suffix cannot start another NS line.  Parallel to
-- `manyHelper-parseNewline-exhaust`.
manyHelper-parseNSLine-exhaust : ∀ (pos : Position) (suffix : List Char) (n : ℕ)
  → SuffixStops isNSLineStart suffix
  → manyHelper parseNSLine pos suffix n
    ≡ just (mkResult [] pos suffix)
manyHelper-parseNSLine-exhaust pos suffix zero     _  = refl
manyHelper-parseNSLine-exhaust pos suffix (suc n') ss
  rewrite parseNSLine-fail-on-stop pos suffix ss = refl

-- ============================================================================
-- Keyword-line concatenation
-- ============================================================================

-- Concatenate a list of keyword strings into a single `List Char` of
-- `"\t<kw1>\n\t<kw2>\n...\t<kwN>\n"`.  Used as the shape parameter of
-- `manyHelper-parseNSLine-body`.
keywordLines-chars : List String → List Char
keywordLines-chars []         = []
keywordLines-chars (kw ∷ kws) =
  '\t' ∷ toList kw ++ₗ '\n' ∷ keywordLines-chars kws

-- Position after consuming one keyword line.
afterKeyword : Position → String → Position
afterKeyword pos kw =
  advancePosition
    (advancePositions (advancePosition pos '\t') (toList kw)) '\n'

-- Position after consuming a sequence of keyword lines.
afterKeywords : Position → List String → Position
afterKeywords pos []         = pos
afterKeywords pos (kw ∷ kws) = afterKeywords (afterKeyword pos kw) kws

-- Each keyword line contributes at least 2 chars (`'\t'` + `'\n'`), so
-- the concatenated-body length always bounds the list length from
-- below.  Used to discharge `suc (length kws) ≤ length input` at the
-- call site without computing the concrete char total.
private
  length-kws-leq-keywordLines :
    ∀ (kws : List String) → length kws ≤ length (keywordLines-chars kws)
  length-kws-leq-keywordLines []         = z≤n
  length-kws-leq-keywordLines (kw ∷ kws)
    rewrite length-++ (toList kw) {'\n' ∷ keywordLines-chars kws} =
    s≤s (≤-trans (length-kws-leq-keywordLines kws)
                  (≤-trans
                    (n≤1+n (length (keywordLines-chars kws)))
                    (m≤n+m (suc (length (keywordLines-chars kws)))
                            (length (toList kw)))))

-- ============================================================================
-- manyHelper-parseNSLine-body — inductive core
-- ============================================================================

-- Given a list of valid keywords whose first chars are all non-hspace,
-- `manyHelper parseNSLine pos (keywordLines-chars kws ++ '\n' ∷ suffix)
-- n` consumes N keyword iterations + 1 blank-line iteration + 0
-- exhaust-iteration, provided fuel `n ≥ suc (length kws)`.  The result
-- list `vs` is not specified (existentially bound); the outer
-- `parseNamespace-roundtrip` discards it via `>>= λ _ → pure tt`.
manyHelper-parseNSLine-body :
  ∀ (pos : Position) (kws : List String) (suffix : List Char) (n : ℕ)
  → All (λ kw → T (validIdentifierᵇ (toList kw))) kws
  → All (λ kw → SuffixStops isHSpace (toList kw)) kws
  → SuffixStops isNSLineStart suffix
  → suc (length kws) ≤ n
  → ∃[ vs ]
       manyHelper parseNSLine pos
         (keywordLines-chars kws ++ₗ '\n' ∷ suffix) n
       ≡ just (mkResult vs
                (advancePosition (afterKeywords pos kws) '\n') suffix)
-- Base case: no keywords — input is `'\n' ∷ suffix`, one blank-branch
-- iteration consumes the `'\n'`, then exhaust on suffix.
manyHelper-parseNSLine-body pos [] suffix (suc n') _ _ ss _ =
    tt ∷ [] ,
    manyHelper-one-iter parseNSLine pos ('\n' ∷ suffix) n'
      tt (advancePosition pos '\n') suffix
      (parseNSLine-blank pos suffix)
      (sameLengthᵇ-cons '\n' suffix)
      (manyHelper-parseNSLine-exhaust (advancePosition pos '\n') suffix n' ss)
-- Inductive case: one keyword iteration via parseNSLine-keyword, then
-- recurse on the shorter tail.
manyHelper-parseNSLine-body pos (kw ∷ kws') suffix (suc n')
    (valid-kw All.∷ valid-rest)
    (hspace-kw All.∷ hspace-rest)
    ss
    (s≤s kws'-bound)
  with manyHelper-parseNSLine-body (afterKeyword pos kw) kws' suffix n'
                                    valid-rest hspace-rest ss kws'-bound
... | vs' , rec-eq =
    tt ∷ vs' , main-eq
  where
    cs : List Char
    cs = toList kw

    rest : List Char
    rest = keywordLines-chars kws' ++ₗ '\n' ∷ suffix

    -- `SuffixStops isHSpace (cs ++ '\n' ∷ rest)` from validity + hspace
    -- stop on kw.  Discharges parseNSLine-keyword's precondition.
    kw-full-ss : SuffixStops isHSpace (cs ++ₗ '\n' ∷ rest)
    kw-full-ss = valid-SuffixStops-++ ('\n' ∷ rest) valid-kw hspace-kw

    kw-iter-eq :
      parseNSLine pos ('\t' ∷ cs ++ₗ '\n' ∷ rest)
      ≡ just (mkResult tt (afterKeyword pos kw) rest)
    kw-iter-eq = parseNSLine-keyword pos cs rest valid-kw kw-full-ss

    -- `keywordLines-chars (kw ∷ kws') ++ '\n' ∷ suffix = '\t' ∷ cs ++
    -- '\n' ∷ rest` after one `++ₗ-assoc` reshape.  The two forms are
    -- propositionally (not definitionally) equal because the `(toList
    -- kw ++ '\n' ∷ keywordLines-chars kws') ++ '\n' ∷ suffix` internal
    -- nesting must be re-associated to `toList kw ++ '\n' ∷
    -- (keywordLines-chars kws' ++ '\n' ∷ suffix)`.
    shape-eq :
      keywordLines-chars (kw ∷ kws') ++ₗ '\n' ∷ suffix
      ≡ '\t' ∷ cs ++ₗ '\n' ∷ rest
    shape-eq =
      cong (_∷_ '\t')
        (++ₗ-assoc (toList kw) ('\n' ∷ keywordLines-chars kws')
                    ('\n' ∷ suffix))

    main-eq :
      manyHelper parseNSLine pos
        (keywordLines-chars (kw ∷ kws') ++ₗ '\n' ∷ suffix) (suc n')
      ≡ just (mkResult (tt ∷ vs')
               (advancePosition (afterKeywords pos (kw ∷ kws')) '\n')
               suffix)
    main-eq =
      trans
        (cong (λ input → manyHelper parseNSLine pos input (suc n'))
              shape-eq)
        (manyHelper-prog-cons parseNSLine pos
          ('\t' ∷ cs ++ₗ '\n' ∷ rest) n'
          tt (afterKeyword pos kw) rest
          vs' (advancePosition (afterKeywords pos (kw ∷ kws')) '\n') suffix
          kw-iter-eq
          (sameLengthᵇ-kw-iter-fail cs rest)
          rec-eq)

-- ============================================================================
-- The 25 canonical NS_ keywords
-- ============================================================================

-- Cantools-canonical 25-keyword set (matches `emitNamespace-chars`).
-- Every keyword is a literal letter-led identifier; the corresponding
-- `validIdentifierᵇ` and `isHSpace` checks reduce to `true` / `false`
-- on the closed strings (verified in `_Scratch.agda`).
nsKeywords : List String
nsKeywords =
  "NS_DESC_" ∷
  "CM_" ∷
  "BA_DEF_" ∷
  "BA_" ∷
  "VAL_" ∷
  "CAT_DEF_" ∷
  "CAT_" ∷
  "FILTER" ∷
  "BA_DEF_DEF_" ∷
  "EV_DATA_" ∷
  "ENVVAR_DATA_" ∷
  "SGTYPE_" ∷
  "SGTYPE_VAL_" ∷
  "BA_DEF_SGTYPE_" ∷
  "BA_SGTYPE_" ∷
  "SIG_TYPE_REF_" ∷
  "VAL_TABLE_" ∷
  "SIG_GROUP_" ∷
  "SIG_VALTYPE_" ∷
  "SIGTYPE_VALTYPE_" ∷
  "BO_TX_BU_" ∷
  "BA_DEF_REL_" ∷
  "BA_REL_" ∷
  "BA_SGTYPE_REL_" ∷
  "SG_MUL_VAL_" ∷
  []

-- Validity: each keyword is a valid identifier.  25 `tt` witnesses
-- closed via reduction.
nsKeywords-valid : All (λ kw → T (validIdentifierᵇ (toList kw))) nsKeywords
nsKeywords-valid =
  tt All.∷ tt All.∷ tt All.∷ tt All.∷ tt All.∷
  tt All.∷ tt All.∷ tt All.∷ tt All.∷ tt All.∷
  tt All.∷ tt All.∷ tt All.∷ tt All.∷ tt All.∷
  tt All.∷ tt All.∷ tt All.∷ tt All.∷ tt All.∷
  tt All.∷ tt All.∷ tt All.∷ tt All.∷ tt All.∷
  All.[]

-- Hspace-stop: each keyword's first char is not hspace.  25 `∷-stop
-- refl` witnesses closed via reduction (first char is a letter).
nsKeywords-hspace-stop :
  All (λ kw → SuffixStops isHSpace (toList kw)) nsKeywords
nsKeywords-hspace-stop =
  ∷-stop refl All.∷ ∷-stop refl All.∷ ∷-stop refl All.∷
  ∷-stop refl All.∷ ∷-stop refl All.∷ ∷-stop refl All.∷
  ∷-stop refl All.∷ ∷-stop refl All.∷ ∷-stop refl All.∷
  ∷-stop refl All.∷ ∷-stop refl All.∷ ∷-stop refl All.∷
  ∷-stop refl All.∷ ∷-stop refl All.∷ ∷-stop refl All.∷
  ∷-stop refl All.∷ ∷-stop refl All.∷ ∷-stop refl All.∷
  ∷-stop refl All.∷ ∷-stop refl All.∷ ∷-stop refl All.∷
  ∷-stop refl All.∷ ∷-stop refl All.∷ ∷-stop refl All.∷
  ∷-stop refl All.∷
  All.[]

-- ============================================================================
-- emitNamespace-chars shape
-- ============================================================================

-- `emitNamespace-chars ++ suffix` reshapes to `toList "NS_" ++ (' ' ∷
-- ':' ∷ '\n' ∷ keywordLines-chars nsKeywords ++ '\n' ∷ suffix)`, ready
-- for the per-step bind chain.  The equality holds definitionally
-- because all sub-strings are closed and the `_++_` associativity
-- unfolds via `primStringToList` reduction.
private
  emitNamespace-chars-shape : ∀ (suffix : List Char)
    → emitNamespace-chars ++ₗ suffix
    ≡ toList "NS_" ++ₗ
        ' ' ∷ ':' ∷ '\n' ∷
        keywordLines-chars nsKeywords ++ₗ '\n' ∷ suffix
  emitNamespace-chars-shape suffix = refl

-- ============================================================================
-- parseNamespace-roundtrip
-- ============================================================================

parseNamespace-roundtrip : ∀ (pos : Position) (suffix : List Char)
  → SuffixStops isNSLineStart suffix
  → parseNamespace pos (emitNamespace-chars ++ₗ suffix)
    ≡ just (mkResult tt
             (advancePositions pos emitNamespace-chars) suffix)
parseNamespace-roundtrip pos suffix ss =
  trans (cong (parseNamespace pos) (emitNamespace-chars-shape suffix))
    (trans step-NS_
      (trans step-parseWSOpt
        (trans step-char-colon
          (trans step-parseNewline
            (trans step-many-parseNSLine
              step-pure)))))
  where
    pos-ns : Position
    pos-ns = advancePositions pos (toList "NS_")

    pos-sp : Position
    pos-sp = advancePosition pos-ns ' '

    pos-colon : Position
    pos-colon = advancePosition pos-sp ':'

    pos-lf1 : Position
    pos-lf1 = advancePosition pos-colon '\n'

    pos-body : Position
    pos-body = advancePosition (afterKeywords pos-lf1 nsKeywords) '\n'

    rest-after-NS_ : List Char
    rest-after-NS_ =
      ' ' ∷ ':' ∷ '\n' ∷ keywordLines-chars nsKeywords ++ₗ '\n' ∷ suffix

    rest-after-WSOpt : List Char
    rest-after-WSOpt =
      ':' ∷ '\n' ∷ keywordLines-chars nsKeywords ++ₗ '\n' ∷ suffix

    rest-after-colon : List Char
    rest-after-colon =
      '\n' ∷ keywordLines-chars nsKeywords ++ₗ '\n' ∷ suffix

    rest-after-LF1 : List Char
    rest-after-LF1 =
      keywordLines-chars nsKeywords ++ₗ '\n' ∷ suffix

    cont-after-NS_ : _ → Parser ⊤
    cont-after-NS_ _ =
      parseWSOpt >>= λ _ →
      char ':' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNSLine >>= λ _ →
      pure tt

    cont-after-WSOpt : _ → Parser ⊤
    cont-after-WSOpt _ =
      char ':' >>= λ _ →
      parseNewline >>= λ _ →
      many parseNSLine >>= λ _ →
      pure tt

    cont-after-colon : _ → Parser ⊤
    cont-after-colon _ =
      parseNewline >>= λ _ →
      many parseNSLine >>= λ _ →
      pure tt

    cont-after-LF1 : _ → Parser ⊤
    cont-after-LF1 _ =
      many parseNSLine >>= λ _ →
      pure tt

    cont-after-many : _ → Parser ⊤
    cont-after-many _ = pure tt

    -- Step 1: string "NS_"
    step-NS_ :
      parseNamespace pos (toList "NS_" ++ₗ rest-after-NS_)
      ≡ cont-after-NS_ "NS_" pos-ns rest-after-NS_
    step-NS_ =
      bind-just-step (string "NS_") cont-after-NS_
                     pos (toList "NS_" ++ₗ rest-after-NS_)
                     "NS_" pos-ns rest-after-NS_
                     (string-success pos "NS_" rest-after-NS_)

    -- Step 2: parseWSOpt consumes 1 space (next is ':').
    wsopt-ss : SuffixStops isHSpace rest-after-WSOpt
    wsopt-ss = ∷-stop refl

    -- `parseWSOpt pos-ns rest-after-NS_ = manyHelper (satisfy isHSpace)
    -- pos-ns rest-after-NS_ (length rest-after-NS_)`, and
    -- `length rest-after-NS_ = suc (length rest-after-WSOpt)` definitionally,
    -- so one iteration consumes the leading space.
    wsopt-eq : parseWSOpt pos-ns rest-after-NS_
             ≡ just (mkResult (' ' ∷ []) pos-sp rest-after-WSOpt)
    wsopt-eq =
      manyHelper-one-iter (satisfy isHSpace) pos-ns
        (' ' ∷ rest-after-WSOpt) (length rest-after-WSOpt)
        ' ' pos-sp rest-after-WSOpt
        refl
        (sameLengthᵇ-cons ' ' rest-after-WSOpt)
        (manyHelper-satisfy-exhaust-many isHSpace pos-sp []
           rest-after-WSOpt All.[] wsopt-ss)

    step-parseWSOpt :
      cont-after-NS_ "NS_" pos-ns rest-after-NS_
      ≡ cont-after-WSOpt (' ' ∷ []) pos-sp rest-after-WSOpt
    step-parseWSOpt =
      bind-just-step parseWSOpt cont-after-WSOpt
                     pos-ns rest-after-NS_
                     (' ' ∷ []) pos-sp rest-after-WSOpt
                     wsopt-eq

    -- Step 3: char ':'
    step-char-colon :
      cont-after-WSOpt (' ' ∷ []) pos-sp rest-after-WSOpt
      ≡ cont-after-colon ':' pos-colon rest-after-colon
    step-char-colon =
      bind-just-step (char ':') cont-after-colon
                     pos-sp rest-after-WSOpt
                     ':' pos-colon rest-after-colon
                     (char-matches ':' pos-sp rest-after-colon)

    -- Step 4: parseNewline consumes '\n'.
    step-parseNewline :
      cont-after-colon ':' pos-colon rest-after-colon
      ≡ cont-after-LF1 '\n' pos-lf1 rest-after-LF1
    step-parseNewline =
      bind-just-step parseNewline cont-after-LF1
                     pos-colon rest-after-colon
                     '\n' pos-lf1 rest-after-LF1
                     (parseNewline-match-LF pos-colon rest-after-LF1)

    -- Step 5: many parseNSLine consumes the 25 keyword lines + 1 blank
    -- line, then terminates on the outer suffix.
    body-res : ∃[ vs ]
       many parseNSLine pos-lf1 rest-after-LF1
       ≡ just (mkResult vs pos-body suffix)
    body-res =
      manyHelper-parseNSLine-body pos-lf1 nsKeywords suffix
        (length rest-after-LF1)
        nsKeywords-valid nsKeywords-hspace-stop ss
        bound
      where
        -- `length rest-after-LF1 = length (keywordLines-chars nsKeywords) +
        -- suc (length suffix)` (by `length-++`), and `length nsKeywords ≤
        -- length (keywordLines-chars nsKeywords)` (each kw line contributes
        -- ≥ 1 char via the `'\t'` prefix).  Chain gives `suc (length
        -- nsKeywords) ≤ length rest-after-LF1`.
        bound : suc (length nsKeywords) ≤ length rest-after-LF1
        bound =
          subst (λ n → suc (length nsKeywords) ≤ n)
                (sym (length-++ (keywordLines-chars nsKeywords)
                                 {'\n' ∷ suffix}))
                (subst (λ k → suc (length nsKeywords) ≤ k)
                       (sym (+-suc
                               (length (keywordLines-chars nsKeywords))
                               (length suffix)))
                       (s≤s (≤-trans
                              (length-kws-leq-keywordLines nsKeywords)
                              (m≤m+n (length (keywordLines-chars nsKeywords))
                                      (length suffix)))))

    step-many-parseNSLine :
      cont-after-LF1 '\n' pos-lf1 rest-after-LF1
      ≡ cont-after-many (proj₁ body-res) pos-body suffix
    step-many-parseNSLine =
      bind-just-step (many parseNSLine) cont-after-many
                     pos-lf1 rest-after-LF1
                     (proj₁ body-res) pos-body suffix
                     (proj₂ body-res)

    -- Step 6: pure tt.  Align the final position with `advancePositions
    -- pos emitNamespace-chars`.
    afterKeywords-advancePositions :
      ∀ (p : Position) (kws : List String)
      → afterKeywords p kws ≡ advancePositions p (keywordLines-chars kws)
    afterKeywords-advancePositions p [] = refl
    afterKeywords-advancePositions p (kw ∷ kws) =
      trans (afterKeywords-advancePositions (afterKeyword p kw) kws)
            (sym (advancePositions-++ (advancePosition p '\t')
                                       (toList kw)
                                       ('\n' ∷ keywordLines-chars kws)))

    -- `pos-lf1` as `advancePositions pos (toList "NS_" ++ ' ' ∷ ':' ∷
    -- '\n' ∷ [])`.  Unfolds by `advancePositions-++` (once) + four
    -- definitional reductions of `advancePositions` on cons/nil.
    pos-lf1-flat :
      pos-lf1
      ≡ advancePositions pos (toList "NS_" ++ₗ ' ' ∷ ':' ∷ '\n' ∷ [])
    pos-lf1-flat =
      sym (advancePositions-++ pos (toList "NS_") (' ' ∷ ':' ∷ '\n' ∷ []))

    final-pos-eq : pos-body ≡ advancePositions pos emitNamespace-chars
    final-pos-eq =
      trans step-afterKws
        (trans step-absorb-trailing-lf
          step-unify-prefix)
      where
        -- Step A: apply afterKeywords-advancePositions to pos-body.
        step-afterKws :
          pos-body
          ≡ advancePosition
              (advancePositions pos-lf1 (keywordLines-chars nsKeywords))
              '\n'
        step-afterKws =
          cong (λ p → advancePosition p '\n')
               (afterKeywords-advancePositions pos-lf1 nsKeywords)

        -- Step B: `advancePosition X '\n' = advancePositions X ('\n' ∷
        -- [])` definitionally, and then combine via advancePositions-++.
        step-absorb-trailing-lf :
          advancePosition
            (advancePositions pos-lf1 (keywordLines-chars nsKeywords))
            '\n'
          ≡ advancePositions pos-lf1
              (keywordLines-chars nsKeywords ++ₗ '\n' ∷ [])
        step-absorb-trailing-lf =
          sym (advancePositions-++ pos-lf1
                (keywordLines-chars nsKeywords) ('\n' ∷ []))

        -- Step C: unfold pos-lf1 to `advancePositions pos prefix`,
        -- combine with body via advancePositions-++, and check the
        -- combined char list equals emitNamespace-chars (definitional
        -- via closed-string reduction).
        step-unify-prefix :
          advancePositions pos-lf1
            (keywordLines-chars nsKeywords ++ₗ '\n' ∷ [])
          ≡ advancePositions pos emitNamespace-chars
        step-unify-prefix =
          trans
            (cong (λ p → advancePositions p
                     (keywordLines-chars nsKeywords ++ₗ '\n' ∷ []))
                  pos-lf1-flat)
            (sym
              (advancePositions-++ pos
                (toList "NS_" ++ₗ ' ' ∷ ':' ∷ '\n' ∷ [])
                (keywordLines-chars nsKeywords ++ₗ '\n' ∷ [])))

    step-pure :
      cont-after-many (proj₁ body-res) pos-body suffix
      ≡ just (mkResult tt (advancePositions pos emitNamespace-chars) suffix)
    step-pure = cong (λ p → just (mkResult tt p suffix)) final-pos-eq
