{-# OPTIONS --without-K #-}

-- Newline-related helpers shared across every Layer-3 commit in B.3.d.
--
-- This module hosts the infrastructure that reasons about
-- `parseNewline` and its use under `many`:
--
--   * `isNewlineStart`              — Bool predicate `c ≈ᵇ '\n' ∨ c ≈ᵇ
--     '\r'`.  Characterises where `many parseNewline` must terminate.
--   * `parseNewline-match-LF`       — `parseNewline pos ('\n' ∷ cs) ≡
--     just …` on a single-LF prefix.
--   * `parseNewline-fail-on-stop`   — `parseNewline pos suffix ≡
--     nothing` under `SuffixStops isNewlineStart suffix`.
--   * `manyHelper-parseNewline-exhaust` — `manyHelper parseNewline pos
--     suffix n ≡ just (mkResult [] pos suffix)` under the same
--     SuffixStops precondition.  Parallels `manyHelper-satisfy-
--     exhaust-many` but for the `<|>`-composed `parseNewline`.
--   * `manyHelper-one-iter`         — generic "one iteration then
--     exhaust" lemma for `manyHelper`, analogous to `bind-just-step`
--     for `_>>=_`.  Abstract in the result components so K-elim stays
--     out of the unification.
--   * `many-parseNewline-one-LF-stop` — specialisation of the generic
--     helper to the single-LF + non-newline-suffix case.  Used by the
--     VERSION / BS_ trailing blank line (`"\n\n"`).
module Aletheia.DBC.TextParser.Properties.Preamble.Newline where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Char using (Char)
open import Data.Char.Base using (_≈ᵇ_)
open import Data.List using (List; []; _∷_) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans)

open import Aletheia.Parser.Combinators using
  (Parser; Position; ParseResult; mkResult; advancePosition;
   pure; _>>=_; _<|>_; _*>_; many; manyHelper;
   char; string; parseCharsSeq; sameLengthᵇ)
open import Aletheia.DBC.TextParser.Lexer using (parseNewline)
open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; []-stop; ∷-stop; sameLengthᵇ-cons)
open import Aletheia.DBC.TextParser.Properties.Primitives using
  (char-matches; alt-right-nothing; bind-nothing)

-- ============================================================================
-- isNewlineStart predicate
-- ============================================================================

-- Characterises where `parseNewline` fails and hence where `many
-- parseNewline` terminates.  A char starts a newline iff it is `'\n'`
-- or `'\r'`; `SuffixStops isNewlineStart suffix` is the standard Layer-3
-- stop-boundary witness.
isNewlineStart : Char → Bool
isNewlineStart c = (c ≈ᵇ '\n') ∨ (c ≈ᵇ '\r')

-- ============================================================================
-- parseNewline succeeds on LF-led input
-- ============================================================================

-- `string "\r\n" *> pure '\n'` fails on `'\n' ∷ cs` because the very
-- first `char '\r'` inside `parseCharsSeq` fails.  Two nested
-- `bind-nothing`s peel off the two outer binds (`*>` and `string`'s
-- inner `>>=`) to expose the failing `char '\r'`.
private
  string-CRLF-*>-fail-on-LF : ∀ (pos : Position) (cs : List Char)
    → (string "\r\n" *> pure '\n') pos ('\n' ∷ cs) ≡ nothing
  string-CRLF-*>-fail-on-LF pos cs =
    bind-nothing (string "\r\n") (λ _ → pure '\n') pos ('\n' ∷ cs)
      (bind-nothing (parseCharsSeq (toList "\r\n"))
         (λ _ → pure "\r\n")
         pos ('\n' ∷ cs)
         parseCharsSeq-CR-fail)
    where
      parseCharsSeq-CR-fail :
        parseCharsSeq (toList "\r\n") pos ('\n' ∷ cs) ≡ nothing
      parseCharsSeq-CR-fail =
        bind-nothing (char '\r')
          (λ x → parseCharsSeq (toList "\n") >>= λ xs → pure (x ∷ xs))
          pos ('\n' ∷ cs)
          refl

-- `parseNewline` on `'\n' ∷ cs` consumes one char, returning `'\n'`
-- with position advanced.  Three-step: left branch fails → `<|>`
-- falls through via `alt-right-nothing` → `char '\n'` matches via
-- `char-matches`.
parseNewline-match-LF : ∀ (pos : Position) (cs : List Char)
  → parseNewline pos ('\n' ∷ cs)
    ≡ just (mkResult '\n' (advancePosition pos '\n') cs)
parseNewline-match-LF pos cs =
  trans (alt-right-nothing (string "\r\n" *> pure '\n') (char '\n')
           pos ('\n' ∷ cs) (string-CRLF-*>-fail-on-LF pos cs))
        (char-matches '\n' pos cs)

-- ============================================================================
-- parseNewline fails on non-newline-led input
-- ============================================================================

-- Split a disjunction ≡ false into its conjuncts.  Needed because the
-- SuffixStops witness arrives via `with` in an outer clause, and
-- with-abstracting on a pattern-bound variable is rejected by Agda.
-- Pulling the case-split into a top-level helper works around this.
private
  ∨-false-split : ∀ {a b : Bool}
    → (a ∨ b) ≡ false → (a ≡ false) × (b ≡ false)
  ∨-false-split {false} {false} _ = refl , refl

-- `parseNewline` fails on an empty input or on a non-newline-led
-- suffix.  The `SuffixStops isNewlineStart` witness says the head (if
-- any) is neither `'\n'` nor `'\r'`; both `<|>` branches therefore fail
-- on their first char.
--
-- The proof uses a helper `parseNewline-fail-on-char` that takes the
-- non-newline witness as an explicit non-pattern-bound argument,
-- sidestepping Agda's "cannot `with` on pattern-bound variable" rule.
private
  parseNewline-fail-on-char : ∀ (pos : Position) (c : Char) (cs : List Char)
    → isNewlineStart c ≡ false
    → parseNewline pos (c ∷ cs) ≡ nothing
  parseNewline-fail-on-char pos c cs h =
    trans (alt-right-nothing (string "\r\n" *> pure '\n') (char '\n')
             pos (c ∷ cs) left-fail)
          char-LF-fail
    where
      ≈LF : (c ≈ᵇ '\n') ≡ false
      ≈LF with ∨-false-split {c ≈ᵇ '\n'} {c ≈ᵇ '\r'} h
      ... | lf , _ = lf

      ≈CR : (c ≈ᵇ '\r') ≡ false
      ≈CR with ∨-false-split {c ≈ᵇ '\n'} {c ≈ᵇ '\r'} h
      ... | _ , cr = cr

      char-CR-fail : char '\r' pos (c ∷ cs) ≡ nothing
      char-CR-fail rewrite ≈CR = refl

      char-LF-fail : char '\n' pos (c ∷ cs) ≡ nothing
      char-LF-fail rewrite ≈LF = refl

      left-fail : (string "\r\n" *> pure '\n') pos (c ∷ cs) ≡ nothing
      left-fail =
        bind-nothing (string "\r\n") (λ _ → pure '\n') pos (c ∷ cs)
          (bind-nothing (parseCharsSeq (toList "\r\n"))
             (λ _ → pure "\r\n")
             pos (c ∷ cs)
             (bind-nothing (char '\r')
                (λ x → parseCharsSeq (toList "\n") >>=
                       λ xs → pure (x ∷ xs))
                pos (c ∷ cs)
                char-CR-fail))

parseNewline-fail-on-stop : ∀ (pos : Position) (suffix : List Char)
  → SuffixStops isNewlineStart suffix
  → parseNewline pos suffix ≡ nothing
parseNewline-fail-on-stop pos [] _ = refl
parseNewline-fail-on-stop pos (c ∷ cs) (∷-stop h) =
  parseNewline-fail-on-char pos c cs h

-- ============================================================================
-- manyHelper lemmas
-- ============================================================================

-- `manyHelper parseNewline` exhausts to the empty list on any fuel `n`
-- when the suffix cannot start another newline.  Parallels
-- `manyHelper-satisfy-exhaust-many` but for the `<|>`-composed
-- `parseNewline`.  This is the Layer-3 workhorse for `many
-- parseNewline` termination — reused wherever a construct's parser
-- ends with `<many parseNewline>`.
manyHelper-parseNewline-exhaust : ∀ (pos : Position) (suffix : List Char)
                                    (n : ℕ)
  → SuffixStops isNewlineStart suffix
  → manyHelper parseNewline pos suffix n
    ≡ just (mkResult [] pos suffix)
manyHelper-parseNewline-exhaust pos suffix zero     _  = refl
manyHelper-parseNewline-exhaust pos suffix (suc n') ss
  rewrite parseNewline-fail-on-stop pos suffix ss = refl

-- Generic `manyHelper` one-iteration lemma: if the first parse succeeds
-- with progress (via sameLengthᵇ-false) and the remaining iterations
-- exhaust, the full call returns a singleton list.  Abstract in the
-- parser result's components to keep K-elim out of the unification.
-- Parallels `bind-just-step` for `_>>=_`.
manyHelper-one-iter : ∀ {A : Set} (p : Parser A) (pos : Position)
                       (input : List Char) (n : ℕ)
                       (v : A) (pos' : Position) (rest : List Char)
  → p pos input ≡ just (mkResult v pos' rest)
  → sameLengthᵇ input rest ≡ false
  → manyHelper p pos' rest n ≡ just (mkResult [] pos' rest)
  → manyHelper p pos input (suc n)
    ≡ just (mkResult (v ∷ []) pos' rest)
manyHelper-one-iter p pos input n v pos' rest peq sleq hpeq
  rewrite peq
        | sleq
        | hpeq
  = refl

-- Generic `manyHelper` "progressing iteration + tail" lemma: generalises
-- `manyHelper-one-iter` to a non-empty tail result `vs`.  Used by the
-- NS_ inductive proof (`manyHelper-parseNSLine-body`) where each
-- keyword line prepends a `tt` to the recursive call's `vs`.
manyHelper-prog-cons : ∀ {A : Set} (p : Parser A) (pos : Position)
                        (input : List Char) (n : ℕ)
                        (v : A) (pos' : Position) (rest : List Char)
                        (vs : List A) (pos-out : Position) (rest-out : List Char)
  → p pos input ≡ just (mkResult v pos' rest)
  → sameLengthᵇ input rest ≡ false
  → manyHelper p pos' rest n ≡ just (mkResult vs pos-out rest-out)
  → manyHelper p pos input (suc n)
    ≡ just (mkResult (v ∷ vs) pos-out rest-out)
manyHelper-prog-cons p pos input n v pos' rest vs pos-out rest-out peq sleq hpeq
  rewrite peq
        | sleq
        | hpeq
  = refl

-- `many parseNewline` consumes exactly one leading `'\n'` and then
-- terminates on a non-newline outer suffix.  Composes parseNewline-
-- match-LF (one-step) + sameLengthᵇ-cons (progress witness) +
-- manyHelper-parseNewline-exhaust (termination) via the generic
-- `manyHelper-one-iter`.  Used for the VERSION / BS_ trailing blank
-- line — both emit `"\n\n"` which parses as `parseNewline *> many
-- parseNewline` with the inner `many` consuming the single trailing
-- `'\n'`.
many-parseNewline-one-LF-stop :
  ∀ (pos : Position) (suffix : List Char) (n : ℕ)
  → SuffixStops isNewlineStart suffix
  → manyHelper parseNewline pos ('\n' ∷ suffix) (suc n)
    ≡ just (mkResult ('\n' ∷ [])
                     (advancePosition pos '\n') suffix)
many-parseNewline-one-LF-stop pos suffix n ss =
  manyHelper-one-iter parseNewline pos ('\n' ∷ suffix) n
    '\n' (advancePosition pos '\n') suffix
    (parseNewline-match-LF pos suffix)
    (sameLengthᵇ-cons '\n' suffix)
    (manyHelper-parseNewline-exhaust
       (advancePosition pos '\n') suffix n ss)
