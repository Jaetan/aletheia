{-# OPTIONS --without-K #-}

-- B.3.d Layer 3 Commit 3c.1 — `parseAttrTypeDecl` roundtrip.
--
-- `parseAttrTypeDecl = parseStringType <|> parseIntType <|> parseFloatType
--                       <|> parseEnumType <|> parseHexType` is the 5-way
-- dispatch over the AT-tag keywords (`STRING`, `INT`, `FLOAT`, `ENUM`,
-- `HEX`).  Every keyword's first char is distinct — `S`, `I`, `F`, `E`,
-- `H` — so cross-keyword failures reduce to `refl` via `parseCharsSeq`'s
-- structural induction on a head-char mismatch.
--
-- Five per-tag roundtrips compose one-or-two embedded sub-parsers along
-- their bind chain:
--   * ATString  — keyword-only (`string-*>-success`).
--   * ATInt     — `parseIntDecRat × 2` separated by `parseWS`.
--   * ATFloat   — `parseDecRat × 2` (always frac form via Shape B emit).
--   * ATEnum    — `parseEnumLabels` (cons-case; empty unsupported by grammar).
--   * ATHex     — `parseNatDecRat × 2` separated by `parseWS`.
--
-- Foundation reused (Tier-A / Tier-B / 3c.0):
--   * `parseCharsSeq-success` / `string-success` / `string-*>-success`
--     (`Properties/Primitives.agda`)
--   * `parseWS-one-space` (`Properties/Primitives.agda`)
--   * `parseStringLit-roundtrip` (`Properties/Primitives.agda`)
--   * `parseIntDecRat-roundtrip-suffix` / `parseNatDecRat-roundtrip-suffix`
--     (`DecRatParse/Properties.agda`, 3c.0 follow-up)
--   * `parseDecRat-roundtrip-suffix` (`DecRatParse/Properties.agda`,
--     3c parser-subsumption)
--   * `bind-just-step`, `bind-nothing`, `alt-right-nothing`, `alt-left-just`

module Aletheia.DBC.TextParser.Properties.Attributes.Type where

open import Data.Bool using (Bool; true; false; T)
open import Data.Char using (Char)
open import Data.Char.Base using (_≈ᵇ_; isDigit)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_) renaming (_++_ to _++ₗ_)
open import Data.List.Properties using () renaming (++-assoc to ++ₗ-assoc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃₂; _,_)
open import Data.String using (String; toList)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; _≢_)

open import Aletheia.Parser.Combinators
  using (Position; Parser; ParseResult; mkResult; advancePosition; advancePositions;
         _>>=_; pure; _<|>_; _*>_; _<*_; string;
         char; many)

open import Aletheia.DBC.Types using
  ( AttrType; ATInt; ATFloat; ATString; ATEnum; ATHex)
open import Aletheia.DBC.DecRat using (DecRat; mkDecRat; fromℤ; IsCanonical)
open import Aletheia.DBC.DecRat.Refinement using
  ( IntDecRat; intDecRatToℤ
  ; NatDecRat; natDecRatToℕ)

open import Aletheia.DBC.TextParser.Attributes
  using (parseAttrTypeDecl;
         parseStringType; parseIntType; parseFloatType;
         parseEnumType; parseHexType;
         parseEnumLabels)
open import Aletheia.DBC.TextParser.DecRatParse using
  (parseDecRat; parseIntDecRat; parseNatDecRat)
open import Aletheia.DBC.TextParser.Lexer using
  (parseWS; parseWSOpt; parseStringLit; isHSpace)

open import Aletheia.DBC.TextFormatter.Attributes
  using (emitAttrType-chars; emitEnumLabels-chars)
open import Aletheia.DBC.TextFormatter.Emitter
  using (digitChar; showInt-chars; showNat-chars; showℤ-dec-chars;
         showℕ-dec-chars; showDecRat-dec-chars; quoteStringLit-chars)

open import Aletheia.DBC.TextParser.Properties.Primitives using
  ( parseWS-one-space
  ; parseStringLit-roundtrip
  ; alt-right-nothing; alt-left-just; bind-nothing
  ; string-success; string-*>-success)
open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  ( bind-just-step
  ; SuffixStops; ∷-stop; []-stop
  ; advancePositions-++
  ; showNat-chars-head
  ; showDecRat-chars-head-dash; showDecRat-chars-head-digit
  ; headOr
  ; parseDecRat-roundtrip-suffix
  ; parseIntDecRat-roundtrip-suffix
  ; parseNatDecRat-roundtrip-suffix)

-- ============================================================================
-- Local helpers — char-class disjointness
-- ============================================================================

private
  -- 10 digit chars are non-hspace (` ` and `\t`).  Closed-Char `≈ᵇ`
  -- comparison reduces to `refl` per case.
  digitChar-not-isHSpace : ∀ d → isHSpace (digitChar d) ≡ false
  digitChar-not-isHSpace 0 = refl
  digitChar-not-isHSpace 1 = refl
  digitChar-not-isHSpace 2 = refl
  digitChar-not-isHSpace 3 = refl
  digitChar-not-isHSpace 4 = refl
  digitChar-not-isHSpace 5 = refl
  digitChar-not-isHSpace 6 = refl
  digitChar-not-isHSpace 7 = refl
  digitChar-not-isHSpace 8 = refl
  digitChar-not-isHSpace 9 = refl
  digitChar-not-isHSpace
    (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) = refl

  -- `'-' isHSpace` reduces to `false` directly.
  dash-not-isHSpace : isHSpace '-' ≡ false
  dash-not-isHSpace = refl

  -- `showInt-chars z` head is non-hspace.  By cases on the sign of `z`:
  --   * `(+ n)`           — `showInt-chars (+ n) = showNat-chars n` —
  --                         head is `digitChar d` for some `d < 10`.
  --   * `-[1+ _ ]`        — `showInt-chars -[1+ _ ] = '-' ∷ ...` —
  --                         head is `'-'`.
  -- Stated as a `SuffixStops` over `showInt-chars z ++ rest` for
  -- direct use as a `parseWS-one-space` precondition.
  showInt-chars-head-stop-isHSpace : ∀ (z : ℤ) (rest : List Char)
    → SuffixStops isHSpace (showInt-chars z ++ₗ rest)
  showInt-chars-head-stop-isHSpace (+ n) rest with showNat-chars-head n
  ... | d , tail , _ , eq =
        subst (λ xs → SuffixStops isHSpace (xs ++ₗ rest))
              (sym eq)
              (∷-stop (digitChar-not-isHSpace d))
  showInt-chars-head-stop-isHSpace -[1+ _ ] rest =
    ∷-stop dash-not-isHSpace

  -- `showNat-chars n` head is non-hspace.  Single-case helper.
  showNat-chars-head-stop-isHSpace : ∀ (n : ℕ) (rest : List Char)
    → SuffixStops isHSpace (showNat-chars n ++ₗ rest)
  showNat-chars-head-stop-isHSpace n rest with showNat-chars-head n
  ... | d , tail , _ , eq =
        subst (λ xs → SuffixStops isHSpace (xs ++ₗ rest))
              (sym eq)
              (∷-stop (digitChar-not-isHSpace d))

  -- `showDecRat-dec-chars d` head is non-hspace.  Three-case helper
  -- mirroring the emitter's sign dispatch.  `(+ zero)` and `(+ suc _)`
  -- yield digit chars via `showDecRat-chars-head-digit`; `-[1+ _ ]`
  -- yields `'-'` via `showDecRat-chars-head-dash`.
  showDecRat-chars-head-stop-isHSpace : ∀ (d : DecRat) (rest : List Char)
    → SuffixStops isHSpace (showDecRat-dec-chars d ++ₗ rest)
  showDecRat-chars-head-stop-isHSpace (mkDecRat (+ zero) a b cx) rest
    with showDecRat-chars-head-digit zero a b cx
  ... | k , tail , _ , eq =
        subst (λ xs → SuffixStops isHSpace (xs ++ₗ rest))
              (sym eq)
              (∷-stop (digitChar-not-isHSpace k))
  showDecRat-chars-head-stop-isHSpace (mkDecRat (+ suc n) a b cx) rest
    with showDecRat-chars-head-digit (suc n) a b cx
  ... | k , tail , _ , eq =
        subst (λ xs → SuffixStops isHSpace (xs ++ₗ rest))
              (sym eq)
              (∷-stop (digitChar-not-isHSpace k))
  showDecRat-chars-head-stop-isHSpace (mkDecRat -[1+ n ] a b cx) rest
    with showDecRat-chars-head-dash n a b cx
  ... | tail , eq =
        subst (λ xs → SuffixStops isHSpace (xs ++ₗ rest))
              (sym eq)
              (∷-stop dash-not-isHSpace)


-- ============================================================================
-- Cross-keyword failure helpers
-- ============================================================================
--
-- Every keyword's first char is distinct — `S` (STRING), `I` (INT), `F`
-- (FLOAT), `E` (ENUM), `H` (HEX) — so `string "X"` on `'Y' ∷ rest` (X ≠ Y
-- on the first char) reduces to `nothing` via `parseCharsSeq`'s
-- structural head-char dispatch.  Each helper is `refl`.

private
  string-STRING-fail-on-I : ∀ (pos : Position) (rest : List Char)
    → string "STRING" pos ('I' ∷ rest) ≡ nothing
  string-STRING-fail-on-I _ _ = refl

  string-STRING-fail-on-F : ∀ (pos : Position) (rest : List Char)
    → string "STRING" pos ('F' ∷ rest) ≡ nothing
  string-STRING-fail-on-F _ _ = refl

  string-STRING-fail-on-E : ∀ (pos : Position) (rest : List Char)
    → string "STRING" pos ('E' ∷ rest) ≡ nothing
  string-STRING-fail-on-E _ _ = refl

  string-STRING-fail-on-H : ∀ (pos : Position) (rest : List Char)
    → string "STRING" pos ('H' ∷ rest) ≡ nothing
  string-STRING-fail-on-H _ _ = refl

  string-INT-fail-on-F : ∀ (pos : Position) (rest : List Char)
    → string "INT" pos ('F' ∷ rest) ≡ nothing
  string-INT-fail-on-F _ _ = refl

  string-INT-fail-on-E : ∀ (pos : Position) (rest : List Char)
    → string "INT" pos ('E' ∷ rest) ≡ nothing
  string-INT-fail-on-E _ _ = refl

  string-INT-fail-on-H : ∀ (pos : Position) (rest : List Char)
    → string "INT" pos ('H' ∷ rest) ≡ nothing
  string-INT-fail-on-H _ _ = refl

  string-FLOAT-fail-on-E : ∀ (pos : Position) (rest : List Char)
    → string "FLOAT" pos ('E' ∷ rest) ≡ nothing
  string-FLOAT-fail-on-E _ _ = refl

  string-FLOAT-fail-on-H : ∀ (pos : Position) (rest : List Char)
    → string "FLOAT" pos ('H' ∷ rest) ≡ nothing
  string-FLOAT-fail-on-H _ _ = refl

  string-ENUM-fail-on-H : ∀ (pos : Position) (rest : List Char)
    → string "ENUM" pos ('H' ∷ rest) ≡ nothing
  string-ENUM-fail-on-H _ _ = refl

-- ============================================================================
-- Per-tag-parser failure lifts via `bind-nothing`
-- ============================================================================

private
  parseStringType-fail-on-I : ∀ (pos : Position) (rest : List Char)
    → parseStringType pos ('I' ∷ rest) ≡ nothing
  parseStringType-fail-on-I pos rest =
    bind-nothing (string "STRING") (λ _ → pure ATString)
                 pos ('I' ∷ rest)
                 (string-STRING-fail-on-I pos rest)

  parseStringType-fail-on-F : ∀ (pos : Position) (rest : List Char)
    → parseStringType pos ('F' ∷ rest) ≡ nothing
  parseStringType-fail-on-F pos rest =
    bind-nothing (string "STRING") (λ _ → pure ATString)
                 pos ('F' ∷ rest)
                 (string-STRING-fail-on-F pos rest)

  parseStringType-fail-on-E : ∀ (pos : Position) (rest : List Char)
    → parseStringType pos ('E' ∷ rest) ≡ nothing
  parseStringType-fail-on-E pos rest =
    bind-nothing (string "STRING") (λ _ → pure ATString)
                 pos ('E' ∷ rest)
                 (string-STRING-fail-on-E pos rest)

  parseStringType-fail-on-H : ∀ (pos : Position) (rest : List Char)
    → parseStringType pos ('H' ∷ rest) ≡ nothing
  parseStringType-fail-on-H pos rest =
    bind-nothing (string "STRING") (λ _ → pure ATString)
                 pos ('H' ∷ rest)
                 (string-STRING-fail-on-H pos rest)

  parseIntType-fail-on-F : ∀ (pos : Position) (rest : List Char)
    → parseIntType pos ('F' ∷ rest) ≡ nothing
  parseIntType-fail-on-F pos rest =
    bind-nothing (string "INT")
                 (λ _ → parseWS >>= λ _ →
                        parseIntDecRat >>= λ mn →
                        parseWS >>= λ _ →
                        parseIntDecRat >>= λ mx →
                        pure (ATInt mn mx))
                 pos ('F' ∷ rest)
                 (string-INT-fail-on-F pos rest)

  parseIntType-fail-on-E : ∀ (pos : Position) (rest : List Char)
    → parseIntType pos ('E' ∷ rest) ≡ nothing
  parseIntType-fail-on-E pos rest =
    bind-nothing (string "INT")
                 (λ _ → parseWS >>= λ _ →
                        parseIntDecRat >>= λ mn →
                        parseWS >>= λ _ →
                        parseIntDecRat >>= λ mx →
                        pure (ATInt mn mx))
                 pos ('E' ∷ rest)
                 (string-INT-fail-on-E pos rest)

  parseIntType-fail-on-H : ∀ (pos : Position) (rest : List Char)
    → parseIntType pos ('H' ∷ rest) ≡ nothing
  parseIntType-fail-on-H pos rest =
    bind-nothing (string "INT")
                 (λ _ → parseWS >>= λ _ →
                        parseIntDecRat >>= λ mn →
                        parseWS >>= λ _ →
                        parseIntDecRat >>= λ mx →
                        pure (ATInt mn mx))
                 pos ('H' ∷ rest)
                 (string-INT-fail-on-H pos rest)

  parseFloatType-fail-on-E : ∀ (pos : Position) (rest : List Char)
    → parseFloatType pos ('E' ∷ rest) ≡ nothing
  parseFloatType-fail-on-E pos rest =
    bind-nothing (string "FLOAT")
                 (λ _ → parseWS >>= λ _ →
                        parseDecRat >>= λ mn →
                        parseWS >>= λ _ →
                        parseDecRat >>= λ mx →
                        pure (ATFloat mn mx))
                 pos ('E' ∷ rest)
                 (string-FLOAT-fail-on-E pos rest)

  parseFloatType-fail-on-H : ∀ (pos : Position) (rest : List Char)
    → parseFloatType pos ('H' ∷ rest) ≡ nothing
  parseFloatType-fail-on-H pos rest =
    bind-nothing (string "FLOAT")
                 (λ _ → parseWS >>= λ _ →
                        parseDecRat >>= λ mn →
                        parseWS >>= λ _ →
                        parseDecRat >>= λ mx →
                        pure (ATFloat mn mx))
                 pos ('H' ∷ rest)
                 (string-FLOAT-fail-on-H pos rest)

  parseEnumType-fail-on-H : ∀ (pos : Position) (rest : List Char)
    → parseEnumType pos ('H' ∷ rest) ≡ nothing
  parseEnumType-fail-on-H pos rest =
    bind-nothing (string "ENUM")
                 (λ _ → parseWS >>= λ _ →
                        parseEnumLabels >>= λ ls →
                        pure (ATEnum ls))
                 pos ('H' ∷ rest)
                 (string-ENUM-fail-on-H pos rest)

-- ============================================================================
-- 5-way <|> dispatch lift helpers
-- ============================================================================
--
-- Given a per-tag parser succeeds at position `(p, r)`, lift through the
-- nested `<|>` chain.  One helper per tag captures the necessary
-- left-failures and the success.

private
  -- ATString — leftmost branch.  Three nested `alt-left-just` lifts.
  lift-STRING : ∀ (pos : Position) (input : List Char) (r : ParseResult AttrType)
    → parseStringType pos input ≡ just r
    → parseAttrTypeDecl pos input ≡ just r
  lift-STRING pos input r p =
    alt-left-just (parseStringType <|> parseIntType <|> parseFloatType <|> parseEnumType)
                  parseHexType pos input r
      (alt-left-just (parseStringType <|> parseIntType <|> parseFloatType)
                     parseEnumType pos input r
        (alt-left-just (parseStringType <|> parseIntType)
                       parseFloatType pos input r
          (alt-left-just parseStringType
                         parseIntType pos input r p)))

  -- ATInt — head 'I'.  parseStringType fails on 'I'; parseIntType
  -- succeeds.  Then 3 outer alt-left-just lifts.
  lift-INT : ∀ (pos : Position) (rest : List Char) (r : ParseResult AttrType)
    → parseIntType pos ('I' ∷ rest) ≡ just r
    → parseAttrTypeDecl pos ('I' ∷ rest) ≡ just r
  lift-INT pos rest r p =
    alt-left-just (parseStringType <|> parseIntType <|> parseFloatType <|> parseEnumType)
                  parseHexType pos ('I' ∷ rest) r
      (alt-left-just (parseStringType <|> parseIntType <|> parseFloatType)
                     parseEnumType pos ('I' ∷ rest) r
        (alt-left-just (parseStringType <|> parseIntType)
                       parseFloatType pos ('I' ∷ rest) r
          (trans (alt-right-nothing parseStringType parseIntType pos ('I' ∷ rest)
                    (parseStringType-fail-on-I pos rest))
                 p)))

  -- ATFloat — head 'F'.  parseStringType + parseIntType fail; parseFloatType
  -- succeeds.  Then 2 outer alt-left-just lifts.
  lift-FLOAT : ∀ (pos : Position) (rest : List Char) (r : ParseResult AttrType)
    → parseFloatType pos ('F' ∷ rest) ≡ just r
    → parseAttrTypeDecl pos ('F' ∷ rest) ≡ just r
  lift-FLOAT pos rest r p =
    alt-left-just (parseStringType <|> parseIntType <|> parseFloatType <|> parseEnumType)
                  parseHexType pos ('F' ∷ rest) r
      (alt-left-just (parseStringType <|> parseIntType <|> parseFloatType)
                     parseEnumType pos ('F' ∷ rest) r
        (trans (alt-right-nothing (parseStringType <|> parseIntType) parseFloatType
                                  pos ('F' ∷ rest)
                  (trans (alt-right-nothing parseStringType parseIntType pos ('F' ∷ rest)
                            (parseStringType-fail-on-F pos rest))
                         (parseIntType-fail-on-F pos rest)))
               p))

  -- ATEnum — head 'E'.  parseStringType + parseIntType + parseFloatType
  -- fail; parseEnumType succeeds.  Then 1 outer alt-left-just lift.
  lift-ENUM : ∀ (pos : Position) (rest : List Char) (r : ParseResult AttrType)
    → parseEnumType pos ('E' ∷ rest) ≡ just r
    → parseAttrTypeDecl pos ('E' ∷ rest) ≡ just r
  lift-ENUM pos rest r p =
    alt-left-just (parseStringType <|> parseIntType <|> parseFloatType <|> parseEnumType)
                  parseHexType pos ('E' ∷ rest) r
      (trans (alt-right-nothing (parseStringType <|> parseIntType <|> parseFloatType)
                                parseEnumType pos ('E' ∷ rest)
               (trans (alt-right-nothing (parseStringType <|> parseIntType) parseFloatType
                                          pos ('E' ∷ rest)
                       (trans (alt-right-nothing parseStringType parseIntType pos ('E' ∷ rest)
                                 (parseStringType-fail-on-E pos rest))
                              (parseIntType-fail-on-E pos rest)))
                      (parseFloatType-fail-on-E pos rest)))
             p)

  -- ATHex — head 'H'.  All four prior parsers fail; parseHexType succeeds.
  lift-HEX : ∀ (pos : Position) (rest : List Char) (r : ParseResult AttrType)
    → parseHexType pos ('H' ∷ rest) ≡ just r
    → parseAttrTypeDecl pos ('H' ∷ rest) ≡ just r
  lift-HEX pos rest r p =
    trans (alt-right-nothing
              (parseStringType <|> parseIntType <|> parseFloatType <|> parseEnumType)
              parseHexType pos ('H' ∷ rest)
            (trans (alt-right-nothing
                       (parseStringType <|> parseIntType <|> parseFloatType)
                       parseEnumType pos ('H' ∷ rest)
                     (trans (alt-right-nothing
                                (parseStringType <|> parseIntType) parseFloatType
                                pos ('H' ∷ rest)
                              (trans (alt-right-nothing parseStringType parseIntType
                                                        pos ('H' ∷ rest)
                                       (parseStringType-fail-on-H pos rest))
                                     (parseIntType-fail-on-H pos rest)))
                            (parseFloatType-fail-on-H pos rest)))
                   (parseEnumType-fail-on-H pos rest)))
          p

-- ============================================================================
-- Per-tag roundtrips
-- ============================================================================

-- ATString — `string "STRING" *> pure ATString`.  Closes via
-- `string-*>-success`.
parseAttrTypeDecl-roundtrip-ATString : ∀ (pos : Position) (suffix : List Char)
  → parseAttrTypeDecl pos (emitAttrType-chars ATString ++ₗ suffix)
    ≡ just (mkResult ATString
              (advancePositions pos (emitAttrType-chars ATString))
              suffix)
parseAttrTypeDecl-roundtrip-ATString pos suffix =
  lift-STRING pos (toList "STRING" ++ₗ suffix)
              (mkResult ATString (advancePositions pos (toList "STRING")) suffix)
              (string-*>-success pos "STRING" ATString suffix)

-- ATInt — `string "INT" >>= parseWS >>= parseIntDecRat (mn) >>= parseWS
-- >>= parseIntDecRat (mx) >>= pure (ATInt mn mx)`.  Closes via 5
-- `bind-just-step` calls plus `string-success` / `parseWS-one-space` /
-- `parseIntDecRat-roundtrip-suffix` leaves.  The 4-fold outer dispatch
-- closes via `lift-INT`.
parseAttrTypeDecl-roundtrip-ATInt :
  ∀ (mn mx : IntDecRat) (pos : Position) (suffix : List Char)
  → SuffixStops isDigit suffix
  → '.' ≢ headOr suffix '_'
  → parseAttrTypeDecl pos (emitAttrType-chars (ATInt mn mx) ++ₗ suffix)
    ≡ just (mkResult (ATInt mn mx)
              (advancePositions pos (emitAttrType-chars (ATInt mn mx)))
              suffix)
parseAttrTypeDecl-roundtrip-ATInt mn mx pos suffix ss not-dot =
  trans (cong (λ input → parseAttrTypeDecl pos input) input-eq)
    (lift-INT pos rest-after-I r pIntType-success)
  where
    cs-mn : List Char
    cs-mn = showInt-chars (intDecRatToℤ mn)

    cs-mx : List Char
    cs-mx = showInt-chars (intDecRatToℤ mx)

    -- Input shape after the leading 'I'.  The parseAttrTypeDecl input
    -- is `'I' ∷ rest-after-I`.
    rest-after-I : List Char
    rest-after-I = 'N' ∷ 'T' ∷ ' ' ∷ cs-mn ++ₗ ' ' ∷ cs-mx ++ₗ suffix

    -- Reshape: `(toList "INT " ++ (cs-mn ++ (' ' ∷ cs-mx))) ++ suffix
    --          ≡ toList "INT " ++ (cs-mn ++ (' ' ∷ (cs-mx ++ suffix)))`.
    -- Two `++ₗ-assoc`s — outer over (toList "INT ", cs-mn ++ ' ' ∷ cs-mx,
    -- suffix), inner over (cs-mn, ' ' ∷ cs-mx, suffix).  The toList
    -- reduces to `'I' ∷ 'N' ∷ 'T' ∷ ' ' ∷ ...` and the cons-prepends
    -- collapse the result to `'I' ∷ rest-after-I` definitionally.
    input-eq : emitAttrType-chars (ATInt mn mx) ++ₗ suffix ≡ 'I' ∷ rest-after-I
    input-eq =
      trans (++ₗ-assoc (toList "INT ") (cs-mn ++ₗ ' ' ∷ cs-mx) suffix)
            (cong (toList "INT " ++ₗ_) (++ₗ-assoc cs-mn (' ' ∷ cs-mx) suffix))

    -- Position trace through parseIntType's bind chain.
    pos-INT : Position
    pos-INT = advancePositions pos (toList "INT")

    pos-WS1 : Position
    pos-WS1 = advancePosition pos-INT ' '

    pos-mn : Position
    pos-mn = advancePositions pos-WS1 cs-mn

    pos-WS2 : Position
    pos-WS2 = advancePosition pos-mn ' '

    pos-mx : Position
    pos-mx = advancePositions pos-WS2 cs-mx

    -- Bridge `pos-mx ≡ advancePositions pos (emitAttrType-chars (ATInt mn mx))`.
    -- Goes via `advancePositions-++` over the three abstract chunks
    -- (`toList "INT "`, `cs-mn`, `' ' ∷ cs-mx`).
    pos-mx-eq : pos-mx ≡ advancePositions pos (emitAttrType-chars (ATInt mn mx))
    pos-mx-eq =
      sym (trans
        (advancePositions-++ pos (toList "INT ") (cs-mn ++ₗ ' ' ∷ cs-mx))
        (trans
          (advancePositions-++ (advancePositions pos (toList "INT "))
                                cs-mn (' ' ∷ cs-mx))
          refl))

    r : ParseResult AttrType
    r = mkResult (ATInt mn mx)
                 (advancePositions pos (emitAttrType-chars (ATInt mn mx)))
                 suffix

    -- Inner parseIntType-on-input lemma.  The input is `toList "INT" ++
    -- (' ' ∷ cs-mn ++ ' ' ∷ cs-mx ++ suffix)` after the input-shape
    -- adjust.  Six-step trans chain via `bind-just-step`:
    --   * string "INT"      → consumes 'I' 'N' 'T'.
    --   * parseWS           → consumes ' '.
    --   * parseIntDecRat    → consumes cs-mn, returns `mn`.
    --   * parseWS           → consumes ' '.
    --   * parseIntDecRat    → consumes cs-mx, returns `mx`.
    --   * pure (ATInt mn mx).
    pIntType-success :
      parseIntType pos ('I' ∷ rest-after-I) ≡ just r
    pIntType-success =
      trans (bind-just-step (string "INT")
              (λ _ → parseWS >>= λ _ →
                     parseIntDecRat >>= λ mn₁ →
                     parseWS >>= λ _ →
                     parseIntDecRat >>= λ mx₁ →
                     pure (ATInt mn₁ mx₁))
              pos ('I' ∷ rest-after-I)
              "INT" pos-INT (' ' ∷ cs-mn ++ₗ ' ' ∷ cs-mx ++ₗ suffix)
              (string-success pos "INT" (' ' ∷ cs-mn ++ₗ ' ' ∷ cs-mx ++ₗ suffix)))
      (trans (bind-just-step parseWS
                (λ _ → parseIntDecRat >>= λ mn₁ →
                       parseWS >>= λ _ →
                       parseIntDecRat >>= λ mx₁ →
                       pure (ATInt mn₁ mx₁))
                pos-INT (' ' ∷ cs-mn ++ₗ ' ' ∷ cs-mx ++ₗ suffix)
                (' ' ∷ []) pos-WS1 (cs-mn ++ₗ ' ' ∷ cs-mx ++ₗ suffix)
                (parseWS-one-space pos-INT (cs-mn ++ₗ ' ' ∷ cs-mx ++ₗ suffix)
                   (showInt-chars-head-stop-isHSpace (intDecRatToℤ mn)
                      (' ' ∷ cs-mx ++ₗ suffix))))
      (trans (bind-just-step parseIntDecRat
                (λ mn₁ → parseWS >>= λ _ →
                         parseIntDecRat >>= λ mx₁ →
                         pure (ATInt mn₁ mx₁))
                pos-WS1 (cs-mn ++ₗ ' ' ∷ cs-mx ++ₗ suffix)
                mn pos-mn (' ' ∷ cs-mx ++ₗ suffix)
                (parseIntDecRat-roundtrip-suffix mn pos-WS1
                   (' ' ∷ cs-mx ++ₗ suffix)
                   (∷-stop refl) (λ ())))
      (trans (bind-just-step parseWS
                (λ _ → parseIntDecRat >>= λ mx₁ →
                       pure (ATInt mn mx₁))
                pos-mn (' ' ∷ cs-mx ++ₗ suffix)
                (' ' ∷ []) pos-WS2 (cs-mx ++ₗ suffix)
                (parseWS-one-space pos-mn (cs-mx ++ₗ suffix)
                   (showInt-chars-head-stop-isHSpace (intDecRatToℤ mx) suffix)))
      (trans (bind-just-step parseIntDecRat
                (λ mx₁ → pure (ATInt mn mx₁))
                pos-WS2 (cs-mx ++ₗ suffix)
                mx pos-mx suffix
                (parseIntDecRat-roundtrip-suffix mx pos-WS2 suffix ss not-dot))
        (cong (λ p → just (mkResult (ATInt mn mx) p suffix))
              pos-mx-eq)))))

-- ATHex — same shape as ATInt but with `parseNatDecRat` (and
-- `showNat-chars` / `showℕ-dec-chars`).  `lift-HEX` is the rightmost
-- branch — 4 cross-keyword failures cascade.
parseAttrTypeDecl-roundtrip-ATHex :
  ∀ (mn mx : NatDecRat) (pos : Position) (suffix : List Char)
  → SuffixStops isDigit suffix
  → '.' ≢ headOr suffix '_'
  → parseAttrTypeDecl pos (emitAttrType-chars (ATHex mn mx) ++ₗ suffix)
    ≡ just (mkResult (ATHex mn mx)
              (advancePositions pos (emitAttrType-chars (ATHex mn mx)))
              suffix)
parseAttrTypeDecl-roundtrip-ATHex mn mx pos suffix ss not-dot =
  trans (cong (λ input → parseAttrTypeDecl pos input) input-eq)
    (lift-HEX pos rest-after-H r pHexType-success)
  where
    cs-mn : List Char
    cs-mn = showNat-chars (natDecRatToℕ mn)

    cs-mx : List Char
    cs-mx = showNat-chars (natDecRatToℕ mx)

    rest-after-H : List Char
    rest-after-H = 'E' ∷ 'X' ∷ ' ' ∷ cs-mn ++ₗ ' ' ∷ cs-mx ++ₗ suffix

    input-eq : emitAttrType-chars (ATHex mn mx) ++ₗ suffix ≡ 'H' ∷ rest-after-H
    input-eq =
      trans (++ₗ-assoc (toList "HEX ") (cs-mn ++ₗ ' ' ∷ cs-mx) suffix)
            (cong (toList "HEX " ++ₗ_) (++ₗ-assoc cs-mn (' ' ∷ cs-mx) suffix))

    pos-HEX : Position
    pos-HEX = advancePositions pos (toList "HEX")

    pos-WS1 : Position
    pos-WS1 = advancePosition pos-HEX ' '

    pos-mn : Position
    pos-mn = advancePositions pos-WS1 cs-mn

    pos-WS2 : Position
    pos-WS2 = advancePosition pos-mn ' '

    pos-mx : Position
    pos-mx = advancePositions pos-WS2 cs-mx

    pos-mx-eq : pos-mx ≡ advancePositions pos (emitAttrType-chars (ATHex mn mx))
    pos-mx-eq =
      sym (trans
        (advancePositions-++ pos (toList "HEX ") (cs-mn ++ₗ ' ' ∷ cs-mx))
        (trans
          (advancePositions-++ (advancePositions pos (toList "HEX "))
                                cs-mn (' ' ∷ cs-mx))
          refl))

    r : ParseResult AttrType
    r = mkResult (ATHex mn mx)
                 (advancePositions pos (emitAttrType-chars (ATHex mn mx)))
                 suffix

    pHexType-success :
      parseHexType pos ('H' ∷ rest-after-H) ≡ just r
    pHexType-success =
      trans (bind-just-step (string "HEX")
              (λ _ → parseWS >>= λ _ →
                     parseNatDecRat >>= λ mn₁ →
                     parseWS >>= λ _ →
                     parseNatDecRat >>= λ mx₁ →
                     pure (ATHex mn₁ mx₁))
              pos ('H' ∷ rest-after-H)
              "HEX" pos-HEX (' ' ∷ cs-mn ++ₗ ' ' ∷ cs-mx ++ₗ suffix)
              (string-success pos "HEX" (' ' ∷ cs-mn ++ₗ ' ' ∷ cs-mx ++ₗ suffix)))
      (trans (bind-just-step parseWS
                (λ _ → parseNatDecRat >>= λ mn₁ →
                       parseWS >>= λ _ →
                       parseNatDecRat >>= λ mx₁ →
                       pure (ATHex mn₁ mx₁))
                pos-HEX (' ' ∷ cs-mn ++ₗ ' ' ∷ cs-mx ++ₗ suffix)
                (' ' ∷ []) pos-WS1 (cs-mn ++ₗ ' ' ∷ cs-mx ++ₗ suffix)
                (parseWS-one-space pos-HEX (cs-mn ++ₗ ' ' ∷ cs-mx ++ₗ suffix)
                   (showNat-chars-head-stop-isHSpace (natDecRatToℕ mn)
                      (' ' ∷ cs-mx ++ₗ suffix))))
      (trans (bind-just-step parseNatDecRat
                (λ mn₁ → parseWS >>= λ _ →
                         parseNatDecRat >>= λ mx₁ →
                         pure (ATHex mn₁ mx₁))
                pos-WS1 (cs-mn ++ₗ ' ' ∷ cs-mx ++ₗ suffix)
                mn pos-mn (' ' ∷ cs-mx ++ₗ suffix)
                (parseNatDecRat-roundtrip-suffix mn pos-WS1
                   (' ' ∷ cs-mx ++ₗ suffix)
                   (∷-stop refl) (λ ())))
      (trans (bind-just-step parseWS
                (λ _ → parseNatDecRat >>= λ mx₁ →
                       pure (ATHex mn mx₁))
                pos-mn (' ' ∷ cs-mx ++ₗ suffix)
                (' ' ∷ []) pos-WS2 (cs-mx ++ₗ suffix)
                (parseWS-one-space pos-mn (cs-mx ++ₗ suffix)
                   (showNat-chars-head-stop-isHSpace (natDecRatToℕ mx) suffix)))
      (trans (bind-just-step parseNatDecRat
                (λ mx₁ → pure (ATHex mn mx₁))
                pos-WS2 (cs-mx ++ₗ suffix)
                mx pos-mx suffix
                (parseNatDecRat-roundtrip-suffix mx pos-WS2 suffix ss not-dot))
        (cong (λ p → just (mkResult (ATHex mn mx) p suffix))
              pos-mx-eq)))))

-- ATFloat — same shape as ATInt but with `parseDecRat` (frac form).
-- `showDecRat-dec-chars` always emits Shape B (`<sign><int>.<frac>`),
-- so `parseDecRatFrac` (left branch of `parseDecRat`) matches; the
-- bare-int branch never fires.  `parseDecRat-roundtrip-suffix` only
-- needs `SuffixStops isDigit suffix` (no `'.' ≢ ...` precondition —
-- the frac form's leading-`.` discrimination is internal).
parseAttrTypeDecl-roundtrip-ATFloat :
  ∀ (mn mx : DecRat) (pos : Position) (suffix : List Char)
  → SuffixStops isDigit suffix
  → parseAttrTypeDecl pos (emitAttrType-chars (ATFloat mn mx) ++ₗ suffix)
    ≡ just (mkResult (ATFloat mn mx)
              (advancePositions pos (emitAttrType-chars (ATFloat mn mx)))
              suffix)
parseAttrTypeDecl-roundtrip-ATFloat mn mx pos suffix ss =
  trans (cong (λ input → parseAttrTypeDecl pos input) input-eq)
    (lift-FLOAT pos rest-after-F r pFloatType-success)
  where
    cs-mn : List Char
    cs-mn = showDecRat-dec-chars mn

    cs-mx : List Char
    cs-mx = showDecRat-dec-chars mx

    rest-after-F : List Char
    rest-after-F = 'L' ∷ 'O' ∷ 'A' ∷ 'T' ∷ ' ' ∷ cs-mn ++ₗ ' ' ∷ cs-mx ++ₗ suffix

    input-eq : emitAttrType-chars (ATFloat mn mx) ++ₗ suffix ≡ 'F' ∷ rest-after-F
    input-eq =
      trans (++ₗ-assoc (toList "FLOAT ") (cs-mn ++ₗ ' ' ∷ cs-mx) suffix)
            (cong (toList "FLOAT " ++ₗ_) (++ₗ-assoc cs-mn (' ' ∷ cs-mx) suffix))

    pos-FLOAT : Position
    pos-FLOAT = advancePositions pos (toList "FLOAT")

    pos-WS1 : Position
    pos-WS1 = advancePosition pos-FLOAT ' '

    pos-mn : Position
    pos-mn = advancePositions pos-WS1 cs-mn

    pos-WS2 : Position
    pos-WS2 = advancePosition pos-mn ' '

    pos-mx : Position
    pos-mx = advancePositions pos-WS2 cs-mx

    pos-mx-eq : pos-mx ≡ advancePositions pos (emitAttrType-chars (ATFloat mn mx))
    pos-mx-eq =
      sym (trans
        (advancePositions-++ pos (toList "FLOAT ") (cs-mn ++ₗ ' ' ∷ cs-mx))
        (trans
          (advancePositions-++ (advancePositions pos (toList "FLOAT "))
                                cs-mn (' ' ∷ cs-mx))
          refl))

    r : ParseResult AttrType
    r = mkResult (ATFloat mn mx)
                 (advancePositions pos (emitAttrType-chars (ATFloat mn mx)))
                 suffix

    pFloatType-success :
      parseFloatType pos ('F' ∷ rest-after-F) ≡ just r
    pFloatType-success =
      trans (bind-just-step (string "FLOAT")
              (λ _ → parseWS >>= λ _ →
                     parseDecRat >>= λ mn₁ →
                     parseWS >>= λ _ →
                     parseDecRat >>= λ mx₁ →
                     pure (ATFloat mn₁ mx₁))
              pos ('F' ∷ rest-after-F)
              "FLOAT" pos-FLOAT (' ' ∷ cs-mn ++ₗ ' ' ∷ cs-mx ++ₗ suffix)
              (string-success pos "FLOAT" (' ' ∷ cs-mn ++ₗ ' ' ∷ cs-mx ++ₗ suffix)))
      (trans (bind-just-step parseWS
                (λ _ → parseDecRat >>= λ mn₁ →
                       parseWS >>= λ _ →
                       parseDecRat >>= λ mx₁ →
                       pure (ATFloat mn₁ mx₁))
                pos-FLOAT (' ' ∷ cs-mn ++ₗ ' ' ∷ cs-mx ++ₗ suffix)
                (' ' ∷ []) pos-WS1 (cs-mn ++ₗ ' ' ∷ cs-mx ++ₗ suffix)
                (parseWS-one-space pos-FLOAT (cs-mn ++ₗ ' ' ∷ cs-mx ++ₗ suffix)
                   (showDecRat-chars-head-stop-isHSpace mn
                      (' ' ∷ cs-mx ++ₗ suffix))))
      (trans (bind-just-step parseDecRat
                (λ mn₁ → parseWS >>= λ _ →
                         parseDecRat >>= λ mx₁ →
                         pure (ATFloat mn₁ mx₁))
                pos-WS1 (cs-mn ++ₗ ' ' ∷ cs-mx ++ₗ suffix)
                mn pos-mn (' ' ∷ cs-mx ++ₗ suffix)
                (parseDecRat-roundtrip-suffix mn pos-WS1
                   (' ' ∷ cs-mx ++ₗ suffix)
                   (∷-stop refl)))
      (trans (bind-just-step parseWS
                (λ _ → parseDecRat >>= λ mx₁ →
                       pure (ATFloat mn mx₁))
                pos-mn (' ' ∷ cs-mx ++ₗ suffix)
                (' ' ∷ []) pos-WS2 (cs-mx ++ₗ suffix)
                (parseWS-one-space pos-mn (cs-mx ++ₗ suffix)
                   (showDecRat-chars-head-stop-isHSpace mx suffix)))
      (trans (bind-just-step parseDecRat
                (λ mx₁ → pure (ATFloat mn mx₁))
                pos-WS2 (cs-mx ++ₗ suffix)
                mx pos-mx suffix
                (parseDecRat-roundtrip-suffix mx pos-WS2 suffix ss))
        (cong (λ p → just (mkResult (ATFloat mn mx) p suffix))
              pos-mx-eq)))))


-- ============================================================================
-- ATEnum — parseEnumLabels roundtrip + ATEnum case
-- ============================================================================
--
-- `parseEnumLabels = parseStringLit >>= λ h → many (char ',' *>
-- parseWSOpt *> parseStringLit) >>= λ t → pure (h ∷ t)` requires at
-- least one label.  The grammar enforces this — `ATEnum []` cannot
-- roundtrip via `parseEnumType`, so the proof pattern-matches on the
-- cons case.

open import Aletheia.Parser.Combinators using (manyHelper; sameLengthᵇ)
open import Data.List using (length)
open import Data.Nat using (_≤_; _<_; z≤n; s≤s)
import Data.Nat

open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (manyHelper-prog-cons)

private
  -- The body parser consumes one `,"y"` segment and returns y.
  parseEnumBody : Parser String
  parseEnumBody = char ',' *> parseWSOpt *> parseStringLit

  -- `commaSep-chars (y ∷ ys) = ',' ∷ "y" ∷ commaSep-chars ys`.  Mirrors
  -- the formatter's foldr.
  commaSep-chars : List String → List Char
  commaSep-chars []       = []
  commaSep-chars (y ∷ ys) = ',' ∷ quoteStringLit-chars y ++ₗ commaSep-chars ys

  -- Formatter shape: `emitEnumLabels-chars (x ∷ xs) ≡ quoteStringLit-
  -- chars x ++ commaSep-chars xs`.  The foldr pattern in
  -- `emitEnumLabels-chars` reduces to `commaSep-chars` by induction.
  emitEnumLabels-chars-shape : ∀ x xs
    → emitEnumLabels-chars (x ∷ xs)
      ≡ quoteStringLit-chars x ++ₗ commaSep-chars xs
  emitEnumLabels-chars-shape x [] = refl
  emitEnumLabels-chars-shape x (y ∷ ys)
    rewrite emitEnumLabels-chars-shape y ys = refl


  -- One iteration of parseEnumBody: consumes `,"y"` (no inner WS) and
  -- returns y.  `parseWSOpt` consumes 0 chars because the next char is
  -- `"`.  Discharge via `bind-just-step` over the 3 sub-parsers.
  parseEnumBody-step : ∀ y pos rest
    → SuffixStops (λ c → c ≈ᵇ '"') rest
    → parseEnumBody pos (',' ∷ quoteStringLit-chars y ++ₗ rest)
      ≡ just (mkResult y
               (advancePositions
                  (advancePosition pos ',')
                  (quoteStringLit-chars y))
               rest)
  parseEnumBody-step y pos rest ss = refl-comma-step
    where
      pos1 : Position
      pos1 = advancePosition pos ','

      step-comma :
        char ',' pos (',' ∷ quoteStringLit-chars y ++ₗ rest)
        ≡ just (mkResult ',' pos1 (quoteStringLit-chars y ++ₗ rest))
      step-comma = refl

      -- parseWSOpt consumes 0 chars on quoted-string-leading input.
      step-wsopt :
        parseWSOpt pos1 (quoteStringLit-chars y ++ₗ rest)
        ≡ just (mkResult []
                 pos1
                 (quoteStringLit-chars y ++ₗ rest))
      step-wsopt = refl

      step-stringLit :
        parseStringLit pos1 (quoteStringLit-chars y ++ₗ rest)
        ≡ just (mkResult y
                 (advancePositions pos1 (quoteStringLit-chars y))
                 rest)
      step-stringLit = parseStringLit-roundtrip pos1 y rest ss

      refl-comma-step :
        parseEnumBody pos (',' ∷ quoteStringLit-chars y ++ₗ rest)
        ≡ just (mkResult y
                 (advancePositions pos1 (quoteStringLit-chars y))
                 rest)
      refl-comma-step =
        trans (bind-just-step (char ',') (λ _ → parseWSOpt *> parseStringLit)
                pos (',' ∷ quoteStringLit-chars y ++ₗ rest)
                ',' pos1 (quoteStringLit-chars y ++ₗ rest)
                step-comma)
        (trans (bind-just-step parseWSOpt (λ _ → parseStringLit)
                  pos1 (quoteStringLit-chars y ++ₗ rest)
                  [] pos1 (quoteStringLit-chars y ++ₗ rest)
                  step-wsopt)
               step-stringLit)


  -- `parseEnumBody pos suffix ≡ nothing` when suffix's head is not `,`.
  -- `parseEnumBody = (char ',' *> parseWSOpt) *> parseStringLit` per
  -- left-associativity of `*>`.  Two `bind-nothing` lifts: the inner
  -- one over `char ',' >>= λ _ → parseWSOpt` (using `char ',` failure),
  -- the outer over `(char ',' *> parseWSOpt) >>= λ _ → parseStringLit`.
  parseEnumBody-fail-on-stop : ∀ pos suffix
    → SuffixStops (λ c → c ≈ᵇ ',') suffix
    → parseEnumBody pos suffix ≡ nothing
  parseEnumBody-fail-on-stop pos [] []-stop =
    bind-nothing (char ',' *> parseWSOpt) (λ _ → parseStringLit)
                 pos []
                 (bind-nothing (char ',') (λ _ → parseWSOpt) pos [] refl)
  parseEnumBody-fail-on-stop pos (c ∷ rest) (∷-stop neq) =
    bind-nothing (char ',' *> parseWSOpt) (λ _ → parseStringLit)
                 pos (c ∷ rest)
                 (bind-nothing (char ',') (λ _ → parseWSOpt) pos (c ∷ rest) char-fails)
    where
      char-fails : char ',' pos (c ∷ rest) ≡ nothing
      char-fails rewrite neq = refl

  -- After consuming `,"y"`, input length decreased by at least 3
  -- (1 for ',' + ≥ 2 for the quoted string).  Use the standard
  -- `sameLengthᵇ-lt` argument: `length rest < length (',' ∷ qsl ++
  -- rest)` (since prepending strictly increases length).
  sameLengthᵇ-lt : ∀ {A : Set} (xs ys : List A)
    → length ys Data.Nat.< length xs
    → sameLengthᵇ xs ys ≡ false
  sameLengthᵇ-lt []       []       ()
  sameLengthᵇ-lt []       (_ ∷ _)  ()
  sameLengthᵇ-lt (_ ∷ _)  []       _       = refl
  sameLengthᵇ-lt (_ ∷ xs) (_ ∷ ys) (s≤s h) = sameLengthᵇ-lt xs ys h

  sameLengthᵇ-after-enum-body : ∀ (y : String) (rest : List Char)
    → sameLengthᵇ
        (',' ∷ quoteStringLit-chars y ++ₗ rest)
        rest
      ≡ false
  sameLengthᵇ-after-enum-body y rest =
    sameLengthᵇ-lt (',' ∷ quoteStringLit-chars y ++ₗ rest) rest
      (s≤s len-rest-≤-prefix)
    where
      open import Data.Nat.Properties using (m≤n+m)
      open import Data.List.Properties using () renaming (length-++ to length-++ₗ)

      len-rest-≤-prefix : length rest Data.Nat.≤
                           length (quoteStringLit-chars y ++ₗ rest)
      len-rest-≤-prefix
        rewrite length-++ₗ (quoteStringLit-chars y) {rest} =
          m≤n+m (length rest) (length (quoteStringLit-chars y))

  -- Helper: derive `SuffixStops (≈ᵇ '"') (commaSep-chars ys ++ suffix)`
  -- from `SuffixStops (≈ᵇ '"') suffix`.  When ys ≠ [], the head is `,`
  -- which is non-quote; when ys = [], falls back to the suffix's
  -- precondition.
  commaSep-suffix-quote-stops : ∀ ys suffix
    → SuffixStops (λ c → c ≈ᵇ '"') suffix
    → SuffixStops (λ c → c ≈ᵇ '"') (commaSep-chars ys ++ₗ suffix)
  commaSep-suffix-quote-stops []       _ ss = ss
  commaSep-suffix-quote-stops (_ ∷ _)  _ _  = ∷-stop refl

  -- Inductive iteration on xs.  Combines the cons-step (parseEnumBody-
  -- step) with the recursive tail call via `manyHelper-prog-cons`.
  -- Empty case dispatches on fuel `m`: zero → base, suc → body fails.
  --
  -- Two SuffixStops preconditions on `suffix`:
  --   * `≈ᵇ ','` — used to fail the body parser (`char ','`) at end.
  --   * `≈ᵇ '"'` — used to terminate `parseStringLit`'s post-quote
  --     `manyHelper` when ys = [] and we re-enter parseEnumBody-step's
  --     suffix.  (For ys = (_ ∷ _), the body's suffix starts with `,`
  --     and the quote-stop is automatic.)
  manyHelper-parseEnumBody-body : ∀ pos xs suffix m
    → SuffixStops (λ c → c ≈ᵇ ',') suffix
    → SuffixStops (λ c → c ≈ᵇ '"') suffix
    → length xs ≤ m
    → manyHelper parseEnumBody pos (commaSep-chars xs ++ₗ suffix) m
      ≡ just (mkResult xs (advancePositions pos (commaSep-chars xs)) suffix)
  manyHelper-parseEnumBody-body pos []       suffix zero    _   _   _ = refl
  manyHelper-parseEnumBody-body pos []       suffix (suc m') ssc _   _
    rewrite parseEnumBody-fail-on-stop pos suffix ssc = refl
  manyHelper-parseEnumBody-body pos (y ∷ ys) suffix (suc m') ssc ssq (s≤s len-le) =
    let
      pos1 : Position
      pos1 = advancePositions
              (advancePosition pos ',')
              (quoteStringLit-chars y)

      ss-y-rest : SuffixStops (λ c → c ≈ᵇ '"') (commaSep-chars ys ++ₗ suffix)
      ss-y-rest = commaSep-suffix-quote-stops ys suffix ssq

      iter-eq : parseEnumBody pos
                  (',' ∷ quoteStringLit-chars y ++ₗ commaSep-chars ys ++ₗ suffix)
                ≡ just (mkResult y pos1 (commaSep-chars ys ++ₗ suffix))
      iter-eq = parseEnumBody-step y pos
                  (commaSep-chars ys ++ₗ suffix) ss-y-rest

      sleq : sameLengthᵇ
                (',' ∷ quoteStringLit-chars y ++ₗ commaSep-chars ys ++ₗ suffix)
                (commaSep-chars ys ++ₗ suffix)
                ≡ false
      sleq = sameLengthᵇ-after-enum-body y (commaSep-chars ys ++ₗ suffix)

      rec-eq : manyHelper parseEnumBody pos1
                  (commaSep-chars ys ++ₗ suffix) m'
               ≡ just (mkResult ys
                       (advancePositions pos1 (commaSep-chars ys)) suffix)
      rec-eq = manyHelper-parseEnumBody-body pos1 ys suffix m' ssc ssq len-le

      pos-fold : advancePositions pos1 (commaSep-chars ys)
                 ≡ advancePositions pos (commaSep-chars (y ∷ ys))
      pos-fold = sym (advancePositions-++
                       (advancePosition pos ',')
                       (quoteStringLit-chars y)
                       (commaSep-chars ys))

      input-reshape-eq :
        commaSep-chars (y ∷ ys) ++ₗ suffix
        ≡ ',' ∷ quoteStringLit-chars y ++ₗ commaSep-chars ys ++ₗ suffix
      input-reshape-eq =
        cong (_∷_ ',')
             (++ₗ-assoc (quoteStringLit-chars y) (commaSep-chars ys) suffix)
    in
      trans (cong (λ input → manyHelper parseEnumBody pos input (suc m'))
                  input-reshape-eq)
        (trans (manyHelper-prog-cons parseEnumBody pos
                  (',' ∷ quoteStringLit-chars y ++ₗ commaSep-chars ys ++ₗ suffix)
                  m'
                  y pos1 (commaSep-chars ys ++ₗ suffix)
                  ys
                  (advancePositions pos1 (commaSep-chars ys)) suffix
                  iter-eq sleq rec-eq)
               (cong (λ p → just (mkResult (y ∷ ys) p suffix))
                     pos-fold))


  -- parseEnumLabels-roundtrip for the cons case.  Composes parseStringLit-
  -- roundtrip (head) + many parseEnumBody (tail).  The empty-list case
  -- can't roundtrip — the parser requires at least one quoted string.
  parseEnumLabels-roundtrip-cons : ∀ x xs pos suffix
    → SuffixStops (λ c → c ≈ᵇ '"') suffix
    → SuffixStops (λ c → c ≈ᵇ ',') suffix
    → parseEnumLabels pos (emitEnumLabels-chars (x ∷ xs) ++ₗ suffix)
      ≡ just (mkResult (x ∷ xs)
                (advancePositions pos (emitEnumLabels-chars (x ∷ xs)))
                suffix)
  parseEnumLabels-roundtrip-cons x xs pos suffix ssq ssc =
    trans
      -- Step A: rewrite the input via the formatter shape.
      (cong (λ input → parseEnumLabels pos (input ++ₗ suffix))
            (emitEnumLabels-chars-shape x xs))
      -- Step B: bind chain.
      (trans
        -- Step B.1: parseStringLit reads x.
        (bind-just-step parseStringLit
          (λ h → many parseEnumBody >>= λ t → pure (h ∷ t))
          pos ((quoteStringLit-chars x ++ₗ commaSep-chars xs) ++ₗ suffix)
          x pos1 (commaSep-chars xs ++ₗ suffix)
          parseStringLit-step)
        -- Step B.2: many parseEnumBody reads xs.
        (trans
          (bind-just-step (many parseEnumBody)
            (λ t → pure (x ∷ t))
            pos1 (commaSep-chars xs ++ₗ suffix)
            xs (advancePositions pos1 (commaSep-chars xs)) suffix
            many-step)
          -- Step B.3: pure (x ∷ xs); position-fold collapses to the
          -- closed-form `advancePositions pos (emitEnumLabels-chars (x ∷ xs))`.
          (cong (λ p → just (mkResult (x ∷ xs) p suffix))
                pos-fold)))
    where
      pos1 : Position
      pos1 = advancePositions pos (quoteStringLit-chars x)

      -- parseStringLit reads x; suffix is `commaSep-chars xs ++ suffix`,
      -- whose head is `,` (xs ≠ []) or the suffix's head (xs = []).
      -- Both have `≈ᵇ '"' ≡ false`.
      ssq-after-x : SuffixStops (λ c → c ≈ᵇ '"') (commaSep-chars xs ++ₗ suffix)
      ssq-after-x = commaSep-suffix-quote-stops xs suffix ssq

      parseStringLit-step :
        parseStringLit pos
          ((quoteStringLit-chars x ++ₗ commaSep-chars xs) ++ₗ suffix)
        ≡ just (mkResult x pos1 (commaSep-chars xs ++ₗ suffix))
      parseStringLit-step =
        trans
          (cong (λ input → parseStringLit pos input)
                (++ₗ-assoc (quoteStringLit-chars x) (commaSep-chars xs) suffix))
          (parseStringLit-roundtrip pos x
            (commaSep-chars xs ++ₗ suffix) ssq-after-x)

      -- many parseEnumBody on `commaSep-chars xs ++ suffix` returns xs
      -- with fuel `length input`.  Length bound via existing nat lemmas
      -- (length xs ≤ length (commaSep-chars xs ++ suffix), since each
      -- y contributes ≥ 3 chars).
      many-step :
        many parseEnumBody pos1 (commaSep-chars xs ++ₗ suffix)
        ≡ just (mkResult xs (advancePositions pos1 (commaSep-chars xs)) suffix)
      many-step =
        manyHelper-parseEnumBody-body pos1 xs suffix
          (length (commaSep-chars xs ++ₗ suffix))
          ssc ssq xs-≤-input-length
        where
          open import Data.Nat.Properties using (m≤n+m; m≤m+n; ≤-trans; n≤1+n)
          open import Data.List.Properties using () renaming (length-++ to length-++ₗ)

          length-xs-≤-commaSep : length xs ≤ length (commaSep-chars xs)
          length-xs-≤-commaSep = go xs
            where
              -- Every cons of `xs` contributes ≥ 1 char (the comma)
              -- plus the quoted string body.  Use `m≤n+m` to absorb
              -- the abstract `length (quoteStringLit-chars y')` into
              -- the upper bound.
              go : ∀ (xs' : List String)
                → length xs' ≤ length (commaSep-chars xs')
              go []        = z≤n
              go (y' ∷ ys')
                rewrite length-++ₗ (quoteStringLit-chars y') {commaSep-chars ys'} =
                  s≤s (≤-trans (go ys')
                        (m≤n+m (length (commaSep-chars ys'))
                               (length (quoteStringLit-chars y'))))

          xs-≤-input-length : length xs ≤
                              length (commaSep-chars xs ++ₗ suffix)
          xs-≤-input-length
            rewrite length-++ₗ (commaSep-chars xs) {suffix} =
              ≤-trans length-xs-≤-commaSep
                (m≤m+n (length (commaSep-chars xs)) (length suffix))

      pos-fold :
        advancePositions pos1 (commaSep-chars xs)
        ≡ advancePositions pos (emitEnumLabels-chars (x ∷ xs))
      pos-fold =
        sym (trans
          (cong (advancePositions pos) (emitEnumLabels-chars-shape x xs))
          (advancePositions-++ pos (quoteStringLit-chars x) (commaSep-chars xs)))


-- ATEnum (cons case) — `string "ENUM" >>= parseWS >>= parseEnumLabels >>=
-- pure (ATEnum)`.  3-step bind chain; parseEnumLabels-roundtrip-cons
-- supplies the labels parse.  4-fold outer dispatch via `lift-ENUM`.
parseAttrTypeDecl-roundtrip-ATEnum :
  ∀ (x : String) (xs : List String) (pos : Position) (suffix : List Char)
  → SuffixStops (λ c → c ≈ᵇ '"') suffix
  → SuffixStops (λ c → c ≈ᵇ ',') suffix
  → parseAttrTypeDecl pos (emitAttrType-chars (ATEnum (x ∷ xs)) ++ₗ suffix)
    ≡ just (mkResult (ATEnum (x ∷ xs))
              (advancePositions pos (emitAttrType-chars (ATEnum (x ∷ xs))))
              suffix)
parseAttrTypeDecl-roundtrip-ATEnum x xs pos suffix ssq ssc =
  trans (cong (λ input → parseAttrTypeDecl pos input) input-eq)
    (lift-ENUM pos rest-after-E r pEnumType-success)
  where
    cs-labels : List Char
    cs-labels = emitEnumLabels-chars (x ∷ xs)

    rest-after-E : List Char
    rest-after-E = 'N' ∷ 'U' ∷ 'M' ∷ ' ' ∷ cs-labels ++ₗ suffix

    -- `emitAttrType-chars (ATEnum xs) = "ENUM " ++ emitEnumLabels-chars xs`
    -- — single ++ₗ-assoc to align suffix.
    input-eq :
      emitAttrType-chars (ATEnum (x ∷ xs)) ++ₗ suffix ≡ 'E' ∷ rest-after-E
    input-eq = ++ₗ-assoc (toList "ENUM ") cs-labels suffix

    pos-ENUM : Position
    pos-ENUM = advancePositions pos (toList "ENUM")

    pos-WS : Position
    pos-WS = advancePosition pos-ENUM ' '

    pos-after-labels : Position
    pos-after-labels = advancePositions pos-WS cs-labels

    pos-eq : pos-after-labels ≡
              advancePositions pos (emitAttrType-chars (ATEnum (x ∷ xs)))
    pos-eq = sym (advancePositions-++ pos (toList "ENUM ") cs-labels)

    r : ParseResult AttrType
    r = mkResult (ATEnum (x ∷ xs))
                 (advancePositions pos (emitAttrType-chars (ATEnum (x ∷ xs))))
                 suffix

    pEnumType-success :
      parseEnumType pos ('E' ∷ rest-after-E) ≡ just r
    pEnumType-success =
      trans (bind-just-step (string "ENUM")
              (λ _ → parseWS >>= λ _ →
                     parseEnumLabels >>= λ ls →
                     pure (ATEnum ls))
              pos ('E' ∷ rest-after-E)
              "ENUM" pos-ENUM (' ' ∷ cs-labels ++ₗ suffix)
              (string-success pos "ENUM" (' ' ∷ cs-labels ++ₗ suffix)))
      (trans (bind-just-step parseWS
                (λ _ → parseEnumLabels >>= λ ls →
                       pure (ATEnum ls))
                pos-ENUM (' ' ∷ cs-labels ++ₗ suffix)
                (' ' ∷ []) pos-WS (cs-labels ++ₗ suffix)
                (parseWS-one-space pos-ENUM (cs-labels ++ₗ suffix)
                   (cs-labels-quote-stop xs suffix)))
      (trans (bind-just-step parseEnumLabels
                (λ ls → pure (ATEnum ls))
                pos-WS (cs-labels ++ₗ suffix)
                (x ∷ xs) pos-after-labels suffix
                (parseEnumLabels-roundtrip-cons x xs pos-WS suffix ssq ssc))
        (cong (λ p → just (mkResult (ATEnum (x ∷ xs)) p suffix))
              pos-eq)))
      where
        -- `emitEnumLabels-chars (x ∷ xs)` head is `"` (the leading
        -- quote of x's quoteStringLit).  isHSpace `"` ≡ false.  Use
        -- the shape lemma to reify the head.
        cs-labels-quote-stop : ∀ (xs : List String) (suffix : List Char)
          → SuffixStops isHSpace (cs-labels ++ₗ suffix)
        cs-labels-quote-stop _ _ = ∷-stop refl

