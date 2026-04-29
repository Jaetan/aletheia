{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.5.d — slim `parseVersion-roundtrip` derived from
-- the universal Format DSL roundtrip.
--
-- Pre-3d.5.d (3a): hand-written ~237-line bind-chain proof through
-- 6 parser primitives.
--
-- Post-3d.5.d-3a: `parseVersion = parse versionFmt >>= λ v → many
-- parseNewline >>= λ _ → pure v` (in `TextParser.Preamble`), and the
-- roundtrip reduces to:
--
--   1. A bridge `emit-versionFmt-eq-emitVersion-chars-prefix` proving
--      DSL emit on `v` (plus a trailing `'\n'`) equals existing
--      `emitVersion-chars v`.
--   2. The universal `parseVersion-format-roundtrip` (from
--      `Format.Preamble`).
--   3. The trailing `many parseNewline` consuming the formatter's
--      section-blank `\n` (via `many-parseNewline-one-LF-stop`).
--   4. Position alignment via one `advancePositions-++` application +
--      the bridge (the 2-stage `pos-eq` pattern from 3d.8 / BU_).
module Aletheia.DBC.TextParser.Properties.Preamble.Version where

open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; length) renaming (_++_ to _++ₗ_)
open import Data.List.Properties using () renaming (++-assoc to ++ₗ-assoc)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Aletheia.Parser.Combinators using
  (Parser; Position; mkResult; advancePosition; advancePositions;
   pure; _>>=_; many)
open import Aletheia.DBC.TextParser.Lexer using (parseNewline)
open import Aletheia.DBC.TextParser.Preamble using (parseVersion)
open import Aletheia.DBC.TextFormatter.Preamble using (emitVersion-chars)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; bind-just-step; advancePositions-++)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart; many-parseNewline-one-LF-stop)

open import Aletheia.DBC.TextParser.Format using
  (Format; emit; parse)
open import Aletheia.DBC.TextParser.Format.Preamble as FmtVer using
  (versionFmt)

parseVersion-roundtrip :
    ∀ (pos : Position) (v : List Char) (suffix : List Char)
  → SuffixStops isNewlineStart suffix
  → parseVersion pos (emitVersion-chars v ++ₗ suffix)
    ≡ just (mkResult v
             (advancePositions pos (emitVersion-chars v))
             suffix)
parseVersion-roundtrip pos v suffix nl-stop =
  trans (cong (λ inp → parseVersion pos (inp ++ₗ suffix)) (sym bridge))
    (trans step-shape
      (trans step-format
        (trans step-many-newline
          step-pure)))
  where
    bridge : emit versionFmt v ++ₗ '\n' ∷ [] ≡ emitVersion-chars v
    bridge = FmtVer.emit-versionFmt-eq-emitVersion-chars-prefix v

    pos-line : Position
    pos-line = advancePositions pos (emit versionFmt v)

    pos-after-nl : Position
    pos-after-nl = advancePosition pos-line '\n'

    cont-line : List Char → Parser (List Char)
    cont-line v' = many parseNewline >>= λ _ → pure v'

    cont-blanks : List Char → Parser (List Char)
    cont-blanks _ = pure v

    -- Step 0: associativity reshape — push `'\n' ∷ []` from outside
    -- the bridge into the input prefix.  After this step the input is
    -- `emit versionFmt v ++ '\n' ∷ suffix`.
    step-shape :
      parseVersion pos ((emit versionFmt v ++ₗ '\n' ∷ []) ++ₗ suffix)
      ≡ parseVersion pos (emit versionFmt v ++ₗ '\n' ∷ suffix)
    step-shape = cong (parseVersion pos)
                      (++ₗ-assoc (emit versionFmt v) ('\n' ∷ []) suffix)

    -- Step 1: parse versionFmt succeeds via the universal roundtrip.
    step-format :
      parseVersion pos (emit versionFmt v ++ₗ '\n' ∷ suffix)
      ≡ cont-line v pos-line ('\n' ∷ suffix)
    step-format =
      bind-just-step (parse versionFmt) cont-line
                     pos (emit versionFmt v ++ₗ '\n' ∷ suffix)
                     v pos-line ('\n' ∷ suffix)
                     (FmtVer.parseVersion-format-roundtrip
                       pos v ('\n' ∷ suffix))

    -- Step 2: many parseNewline consumes the leading `'\n'` from the
    -- residual `'\n' ∷ suffix` and stops on the outer non-newline-led
    -- suffix.
    step-many-newline :
      cont-line v pos-line ('\n' ∷ suffix)
      ≡ cont-blanks ('\n' ∷ []) pos-after-nl suffix
    step-many-newline =
      bind-just-step (many parseNewline) cont-blanks
                     pos-line ('\n' ∷ suffix)
                     ('\n' ∷ []) pos-after-nl suffix
                     (many-parseNewline-one-LF-stop
                       pos-line suffix (length suffix) nl-stop)

    -- Step 3: pure v returns just (mkResult v pos-after-nl suffix);
    -- collapse `pos-after-nl` to `advancePositions pos (emitVersion-
    -- chars v)` via 2-stage pos-eq (BU_ pattern).
    pos-eq : pos-after-nl ≡ advancePositions pos (emitVersion-chars v)
    pos-eq =
      trans
        (sym (advancePositions-++ pos (emit versionFmt v) ('\n' ∷ [])))
        (cong (advancePositions pos) bridge)

    step-pure :
      cont-blanks ('\n' ∷ []) pos-after-nl suffix
      ≡ just (mkResult v
               (advancePositions pos (emitVersion-chars v))
               suffix)
    step-pure = cong (λ p → just (mkResult v p suffix)) pos-eq
