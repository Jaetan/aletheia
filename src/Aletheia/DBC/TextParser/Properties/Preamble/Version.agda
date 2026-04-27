{-# OPTIONS --safe --without-K #-}

-- `parseVersion-roundtrip` — per-line-construct roundtrip for the
-- `VERSION "..."` preamble line (B.3.d Layer 3).
--
-- First Layer-3 construct; template-validates the bind-chain
-- composition pattern used by every subsequent per-construct lemma.
--
-- Bind chain (matches `Aletheia.DBC.TextParser.Preamble.parseVersion`):
--
--   string "VERSION" >>= λ _ →
--   parseWS          >>= λ _ →
--   parseStringLit   >>= λ v →
--   parseNewline     >>= λ _ →
--   many parseNewline >>= λ _ →
--   pure v
--
-- Precondition: `SuffixStops isNewlineStart suffix` — the outer suffix
-- must not start with a newline (otherwise `many parseNewline` would
-- over-consume into the next construct).
module Aletheia.DBC.TextParser.Properties.Preamble.Version where

open import Data.Char using (Char)
open import Data.Char.Base using (_≈ᵇ_)
open import Data.List using (List; []; _∷_; length) renaming (_++_ to _++ₗ_)
open import Data.List.Properties using () renaming (++-assoc to ++ₗ-assoc)
open import Data.Maybe using (just)
open import Data.String using (String; toList)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Aletheia.Parser.Combinators using
  (Parser; Position; mkResult; advancePosition; advancePositions;
   pure; _>>=_; string; many)
open import Aletheia.DBC.TextParser.Lexer using
  (parseStringLit; parseWS; parseNewline; isHSpace)
open import Aletheia.DBC.TextParser.Preamble using (parseVersion)
open import Aletheia.DBC.TextFormatter.Preamble using (emitVersion-chars)
open import Aletheia.DBC.TextFormatter.Emitter using (quoteStringLit-chars)
open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; ∷-stop; bind-just-step; advancePositions-++)
open import Aletheia.DBC.TextParser.Properties.Primitives using
  (string-success; parseWS-one-space; parseStringLit-roundtrip)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart; parseNewline-match-LF; many-parseNewline-one-LF-stop)

-- Shape lemma: reassociate `emitVersion-chars v ++ suffix` into the
-- form the per-step bind chain consumes.  Two ++-assoc applications
-- peel off the outer and inner append; the remaining equality holds by
-- closed-string primStringToList reduction.
-- Post-3d.4 + JSON-mirror: `v : List Char` (was `String`); the parser
-- returns and the formatter takes the raw chars.  Proof structure is
-- otherwise unchanged.
private
  emitVersion-chars-shape : ∀ (v : List Char) (suffix : List Char)
    → (toList "VERSION " ++ₗ quoteStringLit-chars v ++ₗ toList "\n\n")
        ++ₗ suffix
    ≡ toList "VERSION"
        ++ₗ ' ' ∷ (quoteStringLit-chars v ++ₗ '\n' ∷ '\n' ∷ suffix)
  emitVersion-chars-shape v suffix =
    trans (++ₗ-assoc (toList "VERSION ")
                     (quoteStringLit-chars v ++ₗ toList "\n\n")
                     suffix)
          (cong (λ xs → toList "VERSION " ++ₗ xs)
                (++ₗ-assoc (quoteStringLit-chars v) (toList "\n\n") suffix))

parseVersion-roundtrip : ∀ (pos : Position) (v : List Char) (suffix : List Char)
  → SuffixStops isNewlineStart suffix
  → parseVersion pos (emitVersion-chars v ++ₗ suffix)
    ≡ just (mkResult v
             (advancePositions pos (emitVersion-chars v))
             suffix)
parseVersion-roundtrip pos v suffix ss =
  trans (cong (parseVersion pos) (emitVersion-chars-shape v suffix))
    (trans step-VERSION
      (trans step-parseWS
        (trans step-parseStringLit
          (trans step-parseNewline
            (trans step-many-parseNewline
              step-pure)))))
  where
    -- Intermediate positions after each parser stage.
    posᵥ : Position
    posᵥ = advancePositions pos (toList "VERSION")

    pos-sp : Position
    pos-sp = advancePosition posᵥ ' '

    pos-sl : Position
    pos-sl = advancePositions pos-sp (quoteStringLit-chars v)

    pos-lf1 : Position
    pos-lf1 = advancePosition pos-sl '\n'

    pos-lf2 : Position
    pos-lf2 = advancePosition pos-lf1 '\n'

    -- Intermediate inputs after each parser stage.
    rest-after-VERSION : List Char
    rest-after-VERSION =
      ' ' ∷ (quoteStringLit-chars v ++ₗ '\n' ∷ '\n' ∷ suffix)

    rest-after-WS : List Char
    rest-after-WS =
      quoteStringLit-chars v ++ₗ '\n' ∷ '\n' ∷ suffix

    rest-after-SL : List Char
    rest-after-SL = '\n' ∷ '\n' ∷ suffix

    rest-after-LF1 : List Char
    rest-after-LF1 = '\n' ∷ suffix

    -- Parser continuations after each bind.  The `Parser` payload is
    -- `List Char` post-3d.4 + JSON-mirror (parseVersion returns the
    -- string-literal body chars directly).
    cont-after-VERSION : String → Parser (List Char)
    cont-after-VERSION _ =
      parseWS >>= λ _ →
      parseStringLit >>= λ v' →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure v'

    cont-after-WS : List Char → Parser (List Char)
    cont-after-WS _ =
      parseStringLit >>= λ v' →
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure v'

    cont-after-SL : List Char → Parser (List Char)
    cont-after-SL v' =
      parseNewline >>= λ _ →
      many parseNewline >>= λ _ →
      pure v'

    cont-after-LF1 : Char → Parser (List Char)
    cont-after-LF1 _ =
      many parseNewline >>= λ _ →
      pure v

    cont-after-manyLF : List Char → Parser (List Char)
    cont-after-manyLF _ = pure v

    -- Step 1: consume "VERSION" via string-success.
    step-VERSION :
      parseVersion pos
        (toList "VERSION" ++ₗ rest-after-VERSION)
      ≡ cont-after-VERSION "VERSION" posᵥ rest-after-VERSION
    step-VERSION =
      bind-just-step (string "VERSION")
                     cont-after-VERSION
                     pos (toList "VERSION" ++ₗ rest-after-VERSION)
                     "VERSION" posᵥ rest-after-VERSION
                     (string-success pos "VERSION" rest-after-VERSION)

    -- Step 2: consume one space via parseWS-one-space.
    -- `quoteStringLit-chars v` definitionally starts with `'"'` (see
    -- `Emitter.quoteStringLit-chars`), so `rest-after-WS` also starts
    -- with `'"'`, and `isHSpace '"' ≡ false` reduces.
    ws-ss : SuffixStops isHSpace rest-after-WS
    ws-ss = ∷-stop refl

    step-parseWS :
      cont-after-VERSION "VERSION" posᵥ rest-after-VERSION
      ≡ cont-after-WS (' ' ∷ []) pos-sp rest-after-WS
    step-parseWS =
      bind-just-step parseWS
                     cont-after-WS
                     posᵥ rest-after-VERSION
                     (' ' ∷ []) pos-sp rest-after-WS
                     (parseWS-one-space posᵥ rest-after-WS ws-ss)

    -- Step 3: consume the string literal via parseStringLit-roundtrip.
    sl-ss : SuffixStops (λ c → c ≈ᵇ '"') rest-after-SL
    sl-ss = ∷-stop refl

    step-parseStringLit :
      cont-after-WS (' ' ∷ []) pos-sp rest-after-WS
      ≡ cont-after-SL v pos-sl rest-after-SL
    step-parseStringLit =
      bind-just-step parseStringLit
                     cont-after-SL
                     pos-sp rest-after-WS
                     v pos-sl rest-after-SL
                     (parseStringLit-roundtrip pos-sp v rest-after-SL sl-ss)

    -- Step 4: consume the first '\n' via parseNewline-match-LF.
    step-parseNewline :
      cont-after-SL v pos-sl rest-after-SL
      ≡ cont-after-LF1 '\n' pos-lf1 rest-after-LF1
    step-parseNewline =
      bind-just-step parseNewline
                     cont-after-LF1
                     pos-sl rest-after-SL
                     '\n' pos-lf1 rest-after-LF1
                     (parseNewline-match-LF pos-sl ('\n' ∷ suffix))

    -- Step 5: consume the second '\n' via many parseNewline, then
    -- terminate on the outer suffix.
    step-many-parseNewline :
      cont-after-LF1 '\n' pos-lf1 rest-after-LF1
      ≡ cont-after-manyLF ('\n' ∷ []) pos-lf2 suffix
    step-many-parseNewline =
      bind-just-step (many parseNewline)
                     cont-after-manyLF
                     pos-lf1 rest-after-LF1
                     ('\n' ∷ []) pos-lf2 suffix
                     (many-parseNewline-one-LF-stop
                        pos-lf1 suffix (length suffix) ss)

    -- Step 6: pure v returns just (mkResult v pos-lf2 suffix).  Align
    -- the final position with the stated `advancePositions pos
    -- (emitVersion-chars v)`.
    final-pos-eq : pos-lf2 ≡ advancePositions pos (emitVersion-chars v)
    final-pos-eq =
      trans (sym (advancePositions-++ pos-sl ('\n' ∷ []) ('\n' ∷ [])))
        (trans (sym (advancePositions-++ pos-sp
                       (quoteStringLit-chars v) ('\n' ∷ '\n' ∷ [])))
          (trans (cong (λ p → advancePositions p
                                (quoteStringLit-chars v ++ₗ '\n' ∷ '\n' ∷ []))
                       (sym (advancePositions-++ posᵥ (' ' ∷ []) [])))
            (trans (sym (advancePositions-++ posᵥ
                           (' ' ∷ [])
                           (quoteStringLit-chars v ++ₗ '\n' ∷ '\n' ∷ [])))
              (sym (advancePositions-++ pos
                      (toList "VERSION")
                      (' ' ∷ (quoteStringLit-chars v
                        ++ₗ '\n' ∷ '\n' ∷ [])))))))

    step-pure :
      cont-after-manyLF ('\n' ∷ []) pos-lf2 suffix
      ≡ just (mkResult v
               (advancePositions pos (emitVersion-chars v))
               suffix)
    step-pure = cong (λ p → just (mkResult v p suffix)) final-pos-eq
