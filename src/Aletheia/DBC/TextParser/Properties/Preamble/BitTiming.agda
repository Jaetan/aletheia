{-# OPTIONS --safe --without-K #-}

-- `parseBitTiming-roundtrip` — per-line-construct roundtrip for the
-- `BS_:` preamble line (B.3.d Layer 3).
--
-- Emitter (canonical empty-body form): `"BS_:\n\n"`.  Parser bind
-- chain (matches `Aletheia.DBC.TextParser.Preamble.parseBitTiming`):
--
--   string "BS_"                        >>= λ _ →
--   parseWSOpt                          >>= λ _ →  -- 0 hspace (next is ':')
--   char ':'                            >>= λ _ →
--   many (satisfy non-newline)          >>= λ _ →  -- 0 chars (next is '\n')
--   parseNewline                        >>= λ _ →
--   many parseNewline                   >>= λ _ →  -- consumes 1 '\n', stops
--   pure tt
--
-- Simpler than VERSION: no embedded `parseStringLit`, no string
-- argument.  New machinery needed is just two zero-iteration `many`
-- consumptions (parseWSOpt, many-non-newline-tail) discharged via
-- `manyHelper-satisfy-exhaust-many`.
module Aletheia.DBC.TextParser.Properties.Preamble.BitTiming where

open import Data.Bool using (Bool; _∨_; not)
open import Data.Char using (Char) renaming (_≟_ to _≟ᶜ_)
open import Data.List using (List; []; _∷_; length) renaming (_++_ to _++ₗ_)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Maybe using (just)
open import Data.String using (toList)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Aletheia.Parser.Combinators using
  (Parser; Position; mkResult; advancePosition; advancePositions;
   pure; _>>=_; string; char; satisfy; many)
open import Aletheia.DBC.TextParser.Lexer using
  (parseWSOpt; parseNewline; isHSpace)
open import Aletheia.DBC.TextParser.Preamble using (parseBitTiming)
open import Aletheia.DBC.TextFormatter.Preamble using (emitBitTiming-chars)
open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; ∷-stop; bind-just-step; manyHelper-satisfy-exhaust-many)
open import Aletheia.DBC.TextParser.Properties.Primitives using
  (char-matches; string-success)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart; parseNewline-match-LF; many-parseNewline-one-LF-stop)

parseBitTiming-roundtrip : ∀ (pos : Position) (suffix : List Char)
  → SuffixStops isNewlineStart suffix
  → parseBitTiming pos (emitBitTiming-chars ++ₗ suffix)
    ≡ just (mkResult tt
             (advancePositions pos emitBitTiming-chars)
             suffix)
parseBitTiming-roundtrip pos suffix ss =
  trans (cong (parseBitTiming pos) input-shape)
    (trans step-BS_
      (trans step-parseWSOpt
        (trans step-char-colon
          (trans step-many-tail
            (trans step-parseNewline
              (trans step-many-parseNewline
                step-pure))))))
  where
    -- Intermediate positions.
    pos-bs : Position
    pos-bs = advancePositions pos (toList "BS_")

    pos-colon : Position
    pos-colon = advancePosition pos-bs ':'

    pos-lf1 : Position
    pos-lf1 = advancePosition pos-colon '\n'

    pos-lf2 : Position
    pos-lf2 = advancePosition pos-lf1 '\n'

    -- Non-newline-char predicate (copied from parseBitTiming's body).
    isNonNewline : Char → Bool
    isNonNewline c = not (⌊ c ≟ᶜ '\n' ⌋ ∨ ⌊ c ≟ᶜ '\r' ⌋)

    -- Intermediate inputs.
    rest-colon-LF-LF : List Char
    rest-colon-LF-LF = ':' ∷ '\n' ∷ '\n' ∷ suffix

    rest-LF-LF : List Char
    rest-LF-LF = '\n' ∷ '\n' ∷ suffix

    rest-LF : List Char
    rest-LF = '\n' ∷ suffix

    -- Input reshaping: `emitBitTiming-chars ++ suffix = toList
    -- "BS_:\n\n" ++ suffix` reduces via primStringToList + ++-on-cons
    -- to `toList "BS_" ++ (':' ∷ '\n' ∷ '\n' ∷ suffix)`.
    input-shape :
      emitBitTiming-chars ++ₗ suffix
      ≡ toList "BS_" ++ₗ rest-colon-LF-LF
    input-shape = refl

    -- Continuations after each bind.
    cont-after-BS_ : _ → Parser ⊤
    cont-after-BS_ _ =
      parseWSOpt >>= λ _ →
      char ':' >>= λ _ →
      many (satisfy isNonNewline) >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure tt

    cont-after-WSOpt : _ → Parser ⊤
    cont-after-WSOpt _ =
      char ':' >>= λ _ →
      many (satisfy isNonNewline) >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure tt

    cont-after-colon : _ → Parser ⊤
    cont-after-colon _ =
      many (satisfy isNonNewline) >>= λ _ →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure tt

    cont-after-many-tail : _ → Parser ⊤
    cont-after-many-tail _ =
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure tt

    cont-after-LF1 : _ → Parser ⊤
    cont-after-LF1 _ =
      many parseNewline >>= λ _ →
      pure tt

    cont-after-many-LF : _ → Parser ⊤
    cont-after-many-LF _ = pure tt

    -- Step 1: string "BS_"
    step-BS_ :
      parseBitTiming pos (toList "BS_" ++ₗ rest-colon-LF-LF)
      ≡ cont-after-BS_ "BS_" pos-bs rest-colon-LF-LF
    step-BS_ =
      bind-just-step (string "BS_")
                     cont-after-BS_
                     pos (toList "BS_" ++ₗ rest-colon-LF-LF)
                     "BS_" pos-bs rest-colon-LF-LF
                     (string-success pos "BS_" rest-colon-LF-LF)

    -- Step 2: parseWSOpt consumes 0 hspace — next char is ':'.
    wsopt-ss : SuffixStops isHSpace rest-colon-LF-LF
    wsopt-ss = ∷-stop refl

    step-parseWSOpt :
      cont-after-BS_ "BS_" pos-bs rest-colon-LF-LF
      ≡ cont-after-WSOpt [] pos-bs rest-colon-LF-LF
    step-parseWSOpt =
      bind-just-step parseWSOpt
                     cont-after-WSOpt
                     pos-bs rest-colon-LF-LF
                     [] pos-bs rest-colon-LF-LF
                     (manyHelper-satisfy-exhaust-many isHSpace pos-bs
                        [] rest-colon-LF-LF All.[] wsopt-ss)

    -- Step 3: char ':'.
    step-char-colon :
      cont-after-WSOpt [] pos-bs rest-colon-LF-LF
      ≡ cont-after-colon ':' pos-colon rest-LF-LF
    step-char-colon =
      bind-just-step (char ':')
                     cont-after-colon
                     pos-bs rest-colon-LF-LF
                     ':' pos-colon rest-LF-LF
                     (char-matches ':' pos-bs rest-LF-LF)

    -- Step 4: many (satisfy isNonNewline) consumes 0 chars — next
    -- char is '\n'.
    nonnewline-ss : SuffixStops isNonNewline rest-LF-LF
    nonnewline-ss = ∷-stop refl

    step-many-tail :
      cont-after-colon ':' pos-colon rest-LF-LF
      ≡ cont-after-many-tail [] pos-colon rest-LF-LF
    step-many-tail =
      bind-just-step (many (satisfy isNonNewline))
                     cont-after-many-tail
                     pos-colon rest-LF-LF
                     [] pos-colon rest-LF-LF
                     (manyHelper-satisfy-exhaust-many isNonNewline pos-colon
                        [] rest-LF-LF All.[] nonnewline-ss)

    -- Step 5: parseNewline consumes the first '\n'.
    step-parseNewline :
      cont-after-many-tail [] pos-colon rest-LF-LF
      ≡ cont-after-LF1 '\n' pos-lf1 rest-LF
    step-parseNewline =
      bind-just-step parseNewline
                     cont-after-LF1
                     pos-colon rest-LF-LF
                     '\n' pos-lf1 rest-LF
                     (parseNewline-match-LF pos-colon rest-LF)

    -- Step 6: many parseNewline consumes the second '\n', then
    -- terminates on the outer suffix.
    step-many-parseNewline :
      cont-after-LF1 '\n' pos-lf1 rest-LF
      ≡ cont-after-many-LF ('\n' ∷ []) pos-lf2 suffix
    step-many-parseNewline =
      bind-just-step (many parseNewline)
                     cont-after-many-LF
                     pos-lf1 rest-LF
                     ('\n' ∷ []) pos-lf2 suffix
                     (many-parseNewline-one-LF-stop
                        pos-lf1 suffix (length suffix) ss)

    -- Step 7: pure tt — position matches `advancePositions pos
    -- emitBitTiming-chars` definitionally (emitter is a closed string).
    final-pos-eq : pos-lf2 ≡ advancePositions pos emitBitTiming-chars
    final-pos-eq = refl

    step-pure :
      cont-after-many-LF ('\n' ∷ []) pos-lf2 suffix
      ≡ just (mkResult tt
               (advancePositions pos emitBitTiming-chars)
               suffix)
    step-pure = cong (λ p → just (mkResult tt p suffix)) final-pos-eq
