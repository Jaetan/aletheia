-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- parseMuxMarker per-tag roundtrips (B.3.d Layer 2 — Tier B).
--
-- Extracted from Properties/Primitives.agda for AGDA-D-15.1 closure (R22
-- continuation of R21 cluster 9).  See Properties/Primitives.agda header
-- for the Layer 2 narrative and the parseStringLit-roundtrip companion.
--
-- Three tags (all statements at the outcome level, `proj₂`):
--   * IsMux       : `proj₂ (parseMuxMarker pos (toList " M" ++ suffix))` →
--                   `just (mkResult IsMux …)`
--   * NotMux      : `proj₂ (parseMuxMarker-left-branch pos suffix) ≡ nothing` →
--                   `just (mkResult NotMux …)`
--   * SelBy v     : `proj₂ (parseMuxMarker pos (toList " m" ++ showℕ-dec-chars v
--                                                 ++ suffix))` →
--                   `just (mkResult (SelBy v) …)`
--
-- Helpers (`alt-left-just`, `alt-right-nothing`, `bind-nothing`,
-- `parseWS-one-space`) are imported from `Properties.Primitives`, which
-- remains the base module.
module Aletheia.DBC.TextParser.Properties.Primitives.MuxMarker where

open import Data.Char using (Char)
open import Data.Char.Base using (_≈ᵇ_; isDigit)
open import Data.List using (List; []; _∷_) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (ℕ)
open import Data.Product using (proj₂)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Aletheia.Parser.Combinators using
  (Parser; Position; mkResult; advancePosition; advancePositions;
   pure; _>>=_; _<|>_; _*>_; char)
open import Aletheia.DBC.TextParser.Lexer using
  (parseWS; parseNatural)
open import Aletheia.DBC.TextParser.Topology.Foundations using
  (parseMuxMarker; MuxMarker; NotMux; IsMux; SelBy; BothMux)
open import Aletheia.DBC.TextFormatter.Emitter using
  (showℕ-dec-chars)
open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; []-stop; ∷-stop; bind-just-step;
   advancePositions-++; parseNatural-showNat-chars)
open import Aletheia.DBC.TextParser.Properties.Primitives using
  (alt-left-just; alt-right-nothing; bind-nothing; parseWS-one-space)

-- IsMux: `" M"` emission.  Layer 3 discharges this when the SG_ mux
-- marker is present.  Note that the precondition on suffix is now
-- against the FIRST character of the inner input (`'M' ∷ suffix`),
-- whose stop predicate `isHSpace 'M' ≡ false` is closed.  Required by
-- the SG_ mux roundtrip (3d.3) where the post-mux suffix is `" : ..."`
-- (starts with hspace), making the original precondition unprovable.
parseMuxMarker-IsMux-roundtrip : ∀ (pos : Position) (suffix : List Char)
  → proj₂ (parseMuxMarker pos (toList " M" ++ₗ suffix))
    ≡ just (mkResult IsMux (advancePositions pos (toList " M")) suffix)
parseMuxMarker-IsMux-roundtrip pos suffix =
  alt-left-just left-branch (pure NotMux) pos
    (' ' ∷ 'M' ∷ suffix) _ step-left
  where
    pos1 : Position
    pos1 = advancePosition pos ' '

    inner : Parser MuxMarker
    inner = (char 'M' *> pure IsMux) <|>
            (char 'm' *> parseNatural >>= λ n →
              (char 'M' *> pure (BothMux n)) <|>
              pure (SelBy n))

    left-branch : Parser MuxMarker
    left-branch = parseWS *> inner

    step-parseWS :
      proj₂ (left-branch pos (' ' ∷ 'M' ∷ suffix))
      ≡ proj₂ (inner pos1 ('M' ∷ suffix))
    step-parseWS =
      bind-just-step parseWS (λ _ → inner)
        pos (' ' ∷ 'M' ∷ suffix)
        (' ' ∷ []) pos1 ('M' ∷ suffix)
        (parseWS-one-space pos ('M' ∷ suffix) (∷-stop refl))

    -- inner reduces on closed 'M' definitionally: char 'M' succeeds,
    -- `pure IsMux` at the advanced position.
    step-inner :
      proj₂ (inner pos1 ('M' ∷ suffix))
      ≡ just (mkResult IsMux (advancePosition pos1 'M') suffix)
    step-inner = refl

    step-left : proj₂ (left-branch pos (' ' ∷ 'M' ∷ suffix))
      ≡ just (mkResult IsMux
               (advancePositions pos (toList " M")) suffix)
    step-left = trans step-parseWS step-inner

-- NotMux: empty emission.  Precondition exposes the whole left branch
-- of parseMuxMarker's `<|>`; Layer 3 discharges it by computing through
-- parseWS + char M / char m failures on the grammar's specific
-- successor characters (e.g. `" :"` for SG_, `" ;"` for EV_).

parseMuxMarker-left-branch : Parser MuxMarker
parseMuxMarker-left-branch =
  parseWS *>
    ((char 'M' *> pure IsMux) <|>
     (char 'm' *> parseNatural >>= λ n →
       (char 'M' *> pure (BothMux n)) <|>
       pure (SelBy n)))

parseMuxMarker-NotMux-roundtrip : ∀ (pos : Position) (suffix : List Char)
  → proj₂ (parseMuxMarker-left-branch pos suffix) ≡ nothing
  → proj₂ (parseMuxMarker pos suffix) ≡ just (mkResult NotMux pos suffix)
parseMuxMarker-NotMux-roundtrip pos suffix eq =
  alt-right-nothing parseMuxMarker-left-branch (pure NotMux) pos suffix eq

-- SelBy: " m<digits>" emission.  Preconditions:
--   * `SuffixStops isHSpace suffix` — parseWS consumes the single leading
--     space, stops at `'m'`.  (Precondition applies to the `suffix`
--     *after* the digit string, but the proof threads `SuffixStops`
--     through the intermediate stages via its structural form.)
--   * `SuffixStops isDigit suffix` — parseNatural stops at the end of
--     the emitted digits, not consuming into `suffix`.
--   * `SuffixStops (λ c → c ≈ᵇ 'M') suffix` — the BothMux branch doesn't
--     fire (suffix doesn't begin with `'M'`).

parseMuxMarker-SelBy-roundtrip : ∀ (pos : Position) (v : ℕ) (suffix : List Char)
  → SuffixStops isDigit suffix
  → SuffixStops (λ c → c ≈ᵇ 'M') suffix
  → proj₂ (parseMuxMarker pos
      (toList " m" ++ₗ showℕ-dec-chars v ++ₗ suffix))
    ≡ just (mkResult (SelBy v)
             (advancePositions pos
                (toList " m" ++ₗ showℕ-dec-chars v))
             suffix)
parseMuxMarker-SelBy-roundtrip pos v suffix digit-stop m-stop =
  alt-left-just left-branch (pure NotMux) pos
    (' ' ∷ 'm' ∷ showℕ-dec-chars v ++ₗ suffix)
    _ step-left
  where
    pos1 : Position
    pos1 = advancePosition pos ' '

    pos2 : Position
    pos2 = advancePosition pos1 'm'

    pos3 : Position
    pos3 = advancePositions pos2 (showℕ-dec-chars v)

    inner : Parser MuxMarker
    inner = (char 'M' *> pure IsMux) <|>
            (char 'm' *> parseNatural >>= λ n →
              (char 'M' *> pure (BothMux n)) <|>
              pure (SelBy n))

    left-branch : Parser MuxMarker
    left-branch = parseWS *> inner

    pos-eq : pos3 ≡ advancePositions pos
                     (toList " m" ++ₗ showℕ-dec-chars v)
    pos-eq =
      sym (advancePositions-++ pos (toList " m") (showℕ-dec-chars v))

    -- char 'M' on suffix returns `nothing`.  Establish this once at the
    -- top by direct pattern-match on `m-stop`.
    char-M-fail : proj₂ (char 'M' pos3 suffix) ≡ nothing
    char-M-fail = char-M-fail-helper suffix m-stop
      where
        char-M-fail-helper : ∀ (xs : List Char)
          → SuffixStops (λ c → c ≈ᵇ 'M') xs
          → proj₂ (char 'M' pos3 xs) ≡ nothing
        char-M-fail-helper [] []-stop = refl
        char-M-fail-helper (c ∷ _) (∷-stop m-false) rewrite m-false = refl

    step-parseWS :
      proj₂ (left-branch pos
        (' ' ∷ 'm' ∷ showℕ-dec-chars v ++ₗ suffix))
      ≡ proj₂ (inner pos1 ('m' ∷ showℕ-dec-chars v ++ₗ suffix))
    step-parseWS =
      bind-just-step parseWS (λ _ → inner)
        pos (' ' ∷ 'm' ∷ showℕ-dec-chars v ++ₗ suffix)
        (' ' ∷ []) pos1 ('m' ∷ showℕ-dec-chars v ++ₗ suffix)
        (parseWS-one-space pos ('m' ∷ showℕ-dec-chars v ++ₗ suffix)
           (∷-stop refl))

    -- char 'M' fails on the closed 'm', so `<|>` steps to the right
    -- branch via `alt-right-nothing` (the pair encoding no longer
    -- reduces `<|>` definitionally past a stuck right branch).
    step-char-m :
      proj₂ (inner pos1 ('m' ∷ showℕ-dec-chars v ++ₗ suffix))
      ≡ proj₂ ((char 'm' *> parseNatural >>= λ n →
                 (char 'M' *> pure (BothMux n)) <|>
                 pure (SelBy n))
                pos1 ('m' ∷ showℕ-dec-chars v ++ₗ suffix))
    step-char-m =
      alt-right-nothing (char 'M' *> pure IsMux)
        (char 'm' *> parseNatural >>= λ n →
          (char 'M' *> pure (BothMux n)) <|>
          pure (SelBy n))
        pos1 ('m' ∷ showℕ-dec-chars v ++ₗ suffix) refl

    -- `char 'm' *> parseNatural` consumes 'm' (closed, via
    -- `bind-just-step` on the pair encoding) then the emitted digits.
    step-charm-nat :
      proj₂ ((char 'm' *> parseNatural)
              pos1 ('m' ∷ showℕ-dec-chars v ++ₗ suffix))
      ≡ just (mkResult v pos3 suffix)
    step-charm-nat =
      trans (bind-just-step (char 'm') (λ _ → parseNatural)
               pos1 ('m' ∷ showℕ-dec-chars v ++ₗ suffix)
               'm' pos2 (showℕ-dec-chars v ++ₗ suffix) refl)
            (parseNatural-showNat-chars pos2 v suffix digit-stop)

    step-parseNat :
      proj₂ ((char 'm' *> parseNatural >>= λ n →
               (char 'M' *> pure (BothMux n)) <|>
               pure (SelBy n))
              pos1 ('m' ∷ showℕ-dec-chars v ++ₗ suffix))
      ≡ proj₂ (((char 'M' *> pure (BothMux v)) <|> pure (SelBy v))
                pos3 suffix)
    step-parseNat =
      bind-just-step (char 'm' *> parseNatural)
        (λ n → (char 'M' *> pure (BothMux n)) <|> pure (SelBy n))
        pos1 ('m' ∷ showℕ-dec-chars v ++ₗ suffix)
        v pos3 suffix
        step-charm-nat

    step-selby :
      proj₂ (((char 'M' *> pure (BothMux v)) <|> pure (SelBy v))
        pos3 suffix)
      ≡ just (mkResult (SelBy v)
               (advancePositions pos
                  (toList " m" ++ₗ showℕ-dec-chars v))
               suffix)
    step-selby =
      trans (alt-right-nothing (char 'M' *> pure (BothMux v))
                               (pure (SelBy v)) pos3 suffix
              (bind-nothing (char 'M') _ pos3 suffix char-M-fail))
            (cong (λ p → just (mkResult (SelBy v) p suffix)) pos-eq)

    step-left : proj₂ (left-branch pos
                  (' ' ∷ 'm' ∷ showℕ-dec-chars v ++ₗ suffix))
                ≡ just (mkResult (SelBy v)
                         (advancePositions pos
                            (toList " m" ++ₗ showℕ-dec-chars v))
                         suffix)
    step-left = trans step-parseWS
                  (trans step-char-m
                    (trans step-parseNat step-selby))
