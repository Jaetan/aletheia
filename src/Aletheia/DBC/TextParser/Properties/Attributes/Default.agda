-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 Commit 3c.2 — `parseRawAttrDefault` per-line construct
-- roundtrip.
--
-- B.3.d Layer 3 3d.5.d 3c-B migration: production parser is now η-style
-- over `attrDefaultFmt` (`Format/AttrLine.agda`):
--
--   parseRawAttrDefault =
--     parse attrDefaultFmt >>= λ result →
--     many parseNewline   >>= λ _ →
--     pure (liftDefaultLine result)
--
--   liftDefaultLine (n, wire-val, _) = mkRawAttrDefault n (liftRavw wire-val)
--
-- Each per-emit-shape dispatcher (RavString / RavDecRatFrac /
-- RavDecRatBareInt) is a thin wrapper over the universal
-- `parseAttrDefault-format-roundtrip` lemma:
--   1. Build the matching `RawAttrValueWire` ctor.
--   2. Build the per-shape `EmitsOK attrValueWireFmt …` via Format/AttrValue's
--      `build-EmitsOK-Ravw*` builders.
--   3. Bridge the dispatcher's inline-char input shape to the Format DSL's
--      canonical `emit attrDefaultFmt ... ++ outer-suffix` (per-shape `cong`
--      of `++-assoc` chains).
--   4. Invoke universal `parseAttrDefault-format-roundtrip`.
--   5. Compose with `bind-just-step` for `many parseNewline → []` (under
--      `SuffixStops isNewlineStart outer-suffix`).
--   6. Lift wire→AST via `liftRavw` at the result.
--
-- Pre-3d.5.d 3c-B: 582 file-LOC hand-written 9-step bind chain + per-shape
-- value-roundtrip helpers + head-stop dispatchers (this file).

module Aletheia.DBC.TextParser.Properties.Attributes.Default where

open import Data.Bool using (false)
open import Data.Char using (Char)
open import Data.Char.Base using (isDigit)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; length) renaming (_++_ to _++ₗ_)
open import Data.List.Properties using () renaming (++-assoc to ++ₗ-assoc)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.String using (toList)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; _≢_)

open import Aletheia.Parser.Combinators
  using (Position; Parser; mkResult; advancePositions;
         _>>=_; pure; many)
open import Aletheia.DBC.DecRat using (DecRat; fromℤ)
open import Aletheia.DBC.DecRat.Refinement using
  (IntDecRat; mkIntDecRatFromℤ; intDecRatToℤ;
   intDecRatToℤ-mkIntDecRatFromℤ)

open import Aletheia.DBC.TextParser.Attributes
  using (parseRawAttrDefault; parseRawAttrValue;
         liftRavw; liftDefaultLine;
         RawAttrDefault; mkRawAttrDefault;
         RavString; RavDecRat)
open import Aletheia.DBC.TextParser.DecRatParse using (parseDecRat)
open import Aletheia.DBC.TextParser.Lexer
  using (parseNewline; parseStringLit)

open import Aletheia.DBC.TextFormatter.Emitter
  using (quoteStringLit-chars; showDecRat-dec-chars; showInt-chars)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (bind-just-step; SuffixStops; ∷-stop; headOr;
   parseDecRat-roundtrip-suffix; parseDecRat-bareInt-roundtrip-suffix)
open import Aletheia.DBC.TextParser.Properties.Primitives using
  (parseStringLit-roundtrip; alt-left-just; alt-right-nothing; bind-nothing)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart; manyHelper-parseNewline-exhaust)

open import Aletheia.DBC.TextParser.Format using
  (Format; emit; parse; EmitsOK)
open import Aletheia.DBC.TextParser.Format.AttrValue using
  (RawAttrValueWire; RavwString; RavwFrac; RavwBareInt;
   attrValueWireFmt;
   build-EmitsOK-RavwString;
   build-EmitsOK-RavwFrac;
   build-EmitsOK-RavwBareInt)
open import Aletheia.DBC.TextParser.Format.AttrLine using
  (attrDefaultFmt; DefaultLineCarrier;
   parseAttrDefault-format-roundtrip)

-- ============================================================================
-- parseStringLit failure on non-quote head — used by parseRawAttrValue-
-- roundtrip-Rav{DecRatFrac,DecRatBareInt} (which dispatch on the alt's
-- right arm under a non-`'"'` head).
-- ============================================================================

private
  open import Aletheia.Parser.Combinators using (char)
    renaming (many to many-parser)
  open import Aletheia.DBC.TextParser.Lexer using (parseStringChar)

  parseStringLit-fail-on-non-quote : ∀ pos c rest
    → (c Data.Char.Base.≈ᵇ '"') ≡ false
    → parseStringLit pos (c ∷ rest) ≡ nothing
  parseStringLit-fail-on-non-quote pos c rest c-eq =
    bind-nothing (char '"')
      (λ _ → many-parser parseStringChar >>= λ chars →
             char '"' >>= λ _ → pure chars)
      pos (c ∷ rest)
      char-fails
    where
      char-fails : char '"' pos (c ∷ rest) ≡ nothing
      char-fails rewrite c-eq = refl

-- ============================================================================
-- parseRawAttrValue per-emit-shape roundtrips — public for use by
-- `Properties/Attributes/Assign/*.agda` (which compose them with each
-- target's bind-chain to handle the value slot of `parseRawAttrAssign` /
-- `parseRawAttrRel`).
-- ============================================================================

-- RavString: parseStringLit succeeds, alt-left-just lifts to parseRawAttrValue.
parseRawAttrValue-roundtrip-RavString :
  ∀ pos s suffix
  → SuffixStops (λ c → c Data.Char.Base.≈ᵇ '"') suffix
  → parseRawAttrValue pos (quoteStringLit-chars s ++ₗ suffix)
    ≡ just (mkResult (RavString s)
              (advancePositions pos (quoteStringLit-chars s))
              suffix)
parseRawAttrValue-roundtrip-RavString pos s suffix ss =
  alt-left-just
    (parseStringLit >>= λ s₁ → pure (RavString s₁))
    (parseDecRat    >>= λ d  → pure (RavDecRat d))
    pos (quoteStringLit-chars s ++ₗ suffix) _
    (bind-just-step parseStringLit (λ s₁ → pure (RavString s₁))
       pos (quoteStringLit-chars s ++ₗ suffix)
       s (advancePositions pos (quoteStringLit-chars s)) suffix
       (parseStringLit-roundtrip pos s suffix ss))

-- RavDecRat (frac form): parseStringLit fails on non-quote head, then
-- parseDecRat (frac wrapper) succeeds.
parseRawAttrValue-roundtrip-RavDecRatFrac :
  ∀ pos d suffix
  → SuffixStops isDigit suffix
  → ∀ c tail
  → showDecRat-dec-chars d ≡ c ∷ tail
  → (c Data.Char.Base.≈ᵇ '"') ≡ false
  → parseRawAttrValue pos (showDecRat-dec-chars d ++ₗ suffix)
    ≡ just (mkResult (RavDecRat d)
              (advancePositions pos (showDecRat-dec-chars d))
              suffix)
parseRawAttrValue-roundtrip-RavDecRatFrac pos d suffix ss-digit c tail head-eq c-not-quote =
  trans
    (alt-right-nothing
       (parseStringLit >>= λ s₁ → pure (RavString s₁))
       (parseDecRat    >>= λ d₁ → pure (RavDecRat d₁))
       pos (showDecRat-dec-chars d ++ₗ suffix)
       (bind-nothing parseStringLit (λ s₁ → pure (RavString s₁))
          pos (showDecRat-dec-chars d ++ₗ suffix)
          (subst (λ chars → parseStringLit pos (chars ++ₗ suffix) ≡ nothing)
                 (sym head-eq)
                 (parseStringLit-fail-on-non-quote pos c (tail ++ₗ suffix) c-not-quote))))
    (bind-just-step parseDecRat (λ d₁ → pure (RavDecRat d₁))
       pos (showDecRat-dec-chars d ++ₗ suffix)
       d (advancePositions pos (showDecRat-dec-chars d)) suffix
       (parseDecRat-roundtrip-suffix d pos suffix ss-digit))

-- RavDecRat (bare-int form, fromℤ z): parseStringLit fails, parseDecRat
-- (bare-int wrapper) succeeds; result value is `fromℤ z`.
parseRawAttrValue-roundtrip-RavDecRatBareInt :
  ∀ pos z suffix
  → SuffixStops isDigit suffix
  → '.' ≢ headOr suffix '_'
  → ∀ c tail
  → showInt-chars z ≡ c ∷ tail
  → (c Data.Char.Base.≈ᵇ '"') ≡ false
  → parseRawAttrValue pos (showInt-chars z ++ₗ suffix)
    ≡ just (mkResult (RavDecRat (fromℤ z))
              (advancePositions pos (showInt-chars z))
              suffix)
parseRawAttrValue-roundtrip-RavDecRatBareInt pos z suffix ss-digit not-dot c tail head-eq c-not-quote =
  trans
    (alt-right-nothing
       (parseStringLit >>= λ s₁ → pure (RavString s₁))
       (parseDecRat    >>= λ d₁ → pure (RavDecRat d₁))
       pos (showInt-chars z ++ₗ suffix)
       (bind-nothing parseStringLit (λ s₁ → pure (RavString s₁))
          pos (showInt-chars z ++ₗ suffix)
          (subst (λ chars → parseStringLit pos (chars ++ₗ suffix) ≡ nothing)
                 (sym head-eq)
                 (parseStringLit-fail-on-non-quote pos c (tail ++ₗ suffix) c-not-quote))))
    (bind-just-step parseDecRat (λ d₁ → pure (RavDecRat d₁))
       pos (showInt-chars z ++ₗ suffix)
       (fromℤ z) (advancePositions pos (showInt-chars z)) suffix
       (parseDecRat-bareInt-roundtrip-suffix z pos suffix ss-digit not-dot))

-- ============================================================================
-- TRACE MODULE — public for Layer 3 Commit 3c.4 (`Properties/Attributes/
-- Line.agda`) to reference end positions in `parseAttrLine-roundtrip-
-- RawDefault-Rav*` result types.
-- ============================================================================

-- The end position after parsing one BA_DEF_DEF_ line.  Equivalent to
-- `advancePositions pos (emit attrDefaultFmt (name, wire-val, tt))` for
-- the matching shape.
module Trace (pos : Position) (name : List Char) (value-chars : List Char)
               (outer-suffix : List Char) where
    cs-name : List Char
    cs-name = quoteStringLit-chars name

    -- Position after the full line emit, computed in the inline-char form
    -- mirror of `emit attrDefaultFmt (n, wire-val, tt)` for backward
    -- compatibility with Layer 4's per-shape line dispatchers.
    pos8 : Position
    pos8 = advancePositions pos
             (toList "BA_DEF_DEF_ " ++ₗ cs-name ++ₗ
              ' ' ∷ value-chars ++ₗ ';' ∷ '\n' ∷ [])

-- ============================================================================
-- Per-shape input bridge — emit attrDefaultFmt (n, wire, tt) ≡ <inline>
-- ============================================================================
--
-- The dispatcher signature uses an inline char-list for the input
-- (`toList "BA_DEF_DEF_ " ++ ... ++ toList ";\n"`).  The universal
-- `parseAttrDefault-format-roundtrip` operates on `emit attrDefaultFmt
-- (n, wire, tt) ++ outer-suffix`.  The bridge converts between the two
-- via `++-assoc` chains and definitional reduction of `emit (withPrefix
-- ...)` / `emit (withWS ...)` / `emit (pair ...)` / `emit (iso ...)`.

private
  -- Common prefix shape: BA_DEF_DEF_ + ' ' + name + ' ' + <value-chars>
  -- + ;\n + outer-suffix.  Both LHS forms reduce to this.
  inline-input : (name value-chars outer-suffix : List Char) → List Char
  inline-input name value-chars outer-suffix =
    toList "BA_DEF_DEF_ " ++ₗ quoteStringLit-chars name ++ₗ
      ' ' ∷ value-chars ++ₗ toList ";\n" ++ₗ outer-suffix

  -- Bridge per shape: `emit attrDefaultFmt (name, wire, tt) ++ outer-suffix
  -- ≡ inline-input name <value-chars> outer-suffix`.
  --
  -- Each shape uses its specific value-chars: `quoteStringLit-chars s`
  -- (RavwString), `showDecRat-dec-chars d` (RavwFrac), `showInt-chars
  -- (intDecRatToℤ z')` (RavwBareInt).
  --
  -- LHS reduces (definitionally) to:
  --   'B' ∷ ... ∷ ' ' ∷ (qsl name ++ ' ' ∷ ((vc ++ ';' ∷ '\n' ∷ []) ++ outer))
  -- RHS reduces (definitionally) to:
  --   'B' ∷ ... ∷ ' ' ∷ (qsl name ++ ' ' ∷ (vc ++ ';' ∷ '\n' ∷ outer))
  -- Difference: `(vc ++ ';' ∷ '\n' ∷ []) ++ outer` vs `vc ++ (';' ∷ '\n' ∷
  -- outer)` — equal by ++-assoc, NOT definitionally.  Bridge is `cong` of
  -- the prefix wrapped around `++-assoc vc (';' ∷ '\n' ∷ []) outer`.

  -- Two ++-assoc steps to rewrite Agda's natural reduction of
  -- `(emit attrDefaultFmt (name, wire, tt)) ++ outer-suffix` (left-
  -- associated via the outer `++ outer`) into the inline-input shape
  -- (right-associated via `toList ";\n" ++ outer`).
  bridge-tail :
    ∀ (name : List Char) (value-chars : List Char) (outer-suffix : List Char)
    → (quoteStringLit-chars name ++ₗ ' ' ∷ (value-chars ++ₗ ';' ∷ '\n' ∷ []))
        ++ₗ outer-suffix
      ≡ quoteStringLit-chars name ++ₗ ' ' ∷ (value-chars ++ₗ ';' ∷ '\n' ∷ outer-suffix)
  bridge-tail name value-chars outer-suffix =
    trans (++ₗ-assoc (quoteStringLit-chars name)
                     (' ' ∷ (value-chars ++ₗ ';' ∷ '\n' ∷ []))
                     outer-suffix)
          (cong (λ z → quoteStringLit-chars name ++ₗ ' ' ∷ z)
                (++ₗ-assoc value-chars (';' ∷ '\n' ∷ []) outer-suffix))

  -- Per-shape bridges: emit attrDefaultFmt (...) ++ outer ≡ inline-input.
  -- The 12-char "BA_DEF_DEF_ " prefix folds in via definitional ++ on
  -- closed-Char ∷-tower; the tail is supplied by `bridge-tail`.

  bridge-RavwString :
    ∀ (name : List Char) (s : List Char) (outer-suffix : List Char)
    → emit attrDefaultFmt (name , RavwString s , tt) ++ₗ outer-suffix
      ≡ inline-input name (quoteStringLit-chars s) outer-suffix
  bridge-RavwString name s outer-suffix =
    cong (λ z → 'B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ ' ' ∷ z)
         (bridge-tail name (quoteStringLit-chars s) outer-suffix)

  bridge-RavwFrac :
    ∀ (name : List Char) (d : DecRat) (outer-suffix : List Char)
    → emit attrDefaultFmt (name , RavwFrac d , tt) ++ₗ outer-suffix
      ≡ inline-input name (showDecRat-dec-chars d) outer-suffix
  bridge-RavwFrac name d outer-suffix =
    cong (λ z → 'B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ ' ' ∷ z)
         (bridge-tail name (showDecRat-dec-chars d) outer-suffix)

  bridge-RavwBareInt :
    ∀ (name : List Char) (z' : IntDecRat) (outer-suffix : List Char)
    → emit attrDefaultFmt (name , RavwBareInt z' , tt) ++ₗ outer-suffix
      ≡ inline-input name (showInt-chars (intDecRatToℤ z')) outer-suffix
  bridge-RavwBareInt name z' outer-suffix =
    cong (λ z → 'B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ ' ' ∷ z)
         (bridge-tail name (showInt-chars (intDecRatToℤ z')) outer-suffix)

-- ============================================================================
-- Per-shape value-suffix EmitsOK
-- ============================================================================
--
-- After parsing the value, the suffix is `;\n + outer-suffix`.  Each
-- shape's EmitsOK precondition holds via `∷-stop refl` on the closed `';'`
-- head: `_≈ᵇ '"'` is false for `';'`, `isDigit` is false for `';'`, and
-- `'.' ≢ headOr (';' ∷ ...) '_'` is `λ ()`.

private
  value-suffix : List Char → List Char
  value-suffix outer-suffix = ';' ∷ '\n' ∷ outer-suffix

  ravwString-emit-OK : ∀ (s : List Char) (outer-suffix : List Char)
    → EmitsOK attrValueWireFmt (RavwString s) (value-suffix outer-suffix)
  ravwString-emit-OK s outer-suffix =
    build-EmitsOK-RavwString s (value-suffix outer-suffix) (∷-stop refl)

  ravwFrac-emit-OK : ∀ (d : DecRat) (outer-suffix : List Char)
    → EmitsOK attrValueWireFmt (RavwFrac d) (value-suffix outer-suffix)
  ravwFrac-emit-OK d outer-suffix =
    build-EmitsOK-RavwFrac d (value-suffix outer-suffix) (∷-stop refl)

  ravwBareInt-emit-OK : ∀ (z : IntDecRat) (outer-suffix : List Char)
    → EmitsOK attrValueWireFmt (RavwBareInt z) (value-suffix outer-suffix)
  ravwBareInt-emit-OK z outer-suffix =
    build-EmitsOK-RavwBareInt z (value-suffix outer-suffix)
                                 (∷-stop refl) (λ ())

-- ============================================================================
-- Common pattern — η-style 3-step composition for any shape
-- ============================================================================
--
-- Given:
--   * `pos` — starting position
--   * `wire-val` — the RawAttrValueWire ctor
--   * EmitsOK witness at `attrValueWireFmt`
--   * `outer-suffix` newline-stopped
-- Produces: parseRawAttrDefault on `emit attrDefaultFmt (name, wire, tt) ++
-- outer-suffix` returns just (mkRawAttrDefault name (liftRavw wire), end-pos,
-- outer-suffix).

private
  parseRawAttrDefault-format-roundtrip-raw :
    ∀ (pos : Position) (name : List Char) (wire-val : RawAttrValueWire)
      (outer-suffix : List Char)
    → SuffixStops isNewlineStart outer-suffix
    → EmitsOK attrValueWireFmt wire-val (value-suffix outer-suffix)
    → parseRawAttrDefault pos
        (emit attrDefaultFmt (name , wire-val , tt) ++ₗ outer-suffix)
      ≡ just (mkResult (mkRawAttrDefault name (liftRavw wire-val))
                (advancePositions pos
                  (emit attrDefaultFmt (name , wire-val , tt)))
                outer-suffix)
  parseRawAttrDefault-format-roundtrip-raw pos name wire-val outer-suffix
                                            ss-NL value-emit =
    trans step-format
      (trans step-many-newline step-pure)
    where
      pos-line : Position
      pos-line = advancePositions pos
                   (emit attrDefaultFmt (name , wire-val , tt))

      cont-line : DefaultLineCarrier → Parser RawAttrDefault
      cont-line c = many parseNewline >>= λ _ → pure (liftDefaultLine c)

      cont-blanks : List Char → Parser RawAttrDefault
      cont-blanks _ = pure (liftDefaultLine (name , wire-val , tt))

      step-format :
        parseRawAttrDefault pos
          (emit attrDefaultFmt (name , wire-val , tt) ++ₗ outer-suffix)
        ≡ cont-line (name , wire-val , tt) pos-line outer-suffix
      step-format =
        bind-just-step (parse attrDefaultFmt) cont-line
          pos
          (emit attrDefaultFmt (name , wire-val , tt) ++ₗ outer-suffix)
          (name , wire-val , tt) pos-line outer-suffix
          (parseAttrDefault-format-roundtrip pos name wire-val outer-suffix
            value-emit)

      step-many-newline :
        cont-line (name , wire-val , tt) pos-line outer-suffix
        ≡ cont-blanks [] pos-line outer-suffix
      step-many-newline =
        bind-just-step (many parseNewline) cont-blanks
          pos-line outer-suffix
          [] pos-line outer-suffix
          (manyHelper-parseNewline-exhaust pos-line outer-suffix
            (length outer-suffix) ss-NL)

      step-pure :
        cont-blanks [] pos-line outer-suffix
        ≡ just (mkResult (mkRawAttrDefault name (liftRavw wire-val))
                  pos-line outer-suffix)
      step-pure = refl

-- ============================================================================
-- TOP-LEVEL DISPATCHERS — 3 cases by emit shape
-- ============================================================================

-- RavString: emit `quoteStringLit-chars s` for the value.
parseRawAttrDefault-roundtrip-RavString :
  ∀ pos (name : List Char) (s : List Char) (outer-suffix : List Char)
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrDefault pos
      (toList "BA_DEF_DEF_ " ++ₗ quoteStringLit-chars name ++ₗ
        ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult (mkRawAttrDefault name (RavString s))
              (Trace.pos8 pos name (quoteStringLit-chars s) outer-suffix)
              outer-suffix)
parseRawAttrDefault-roundtrip-RavString pos name s outer-suffix ss-NL =
  trans (cong (parseRawAttrDefault pos)
              (sym (bridge-RavwString name s outer-suffix)))
    (parseRawAttrDefault-format-roundtrip-raw pos name (RavwString s)
       outer-suffix ss-NL (ravwString-emit-OK s outer-suffix))

-- RavDecRat (frac form): emit `showDecRat-dec-chars d` for the value.
parseRawAttrDefault-roundtrip-RavDecRatFrac :
  ∀ pos (name : List Char) (d : DecRat) (outer-suffix : List Char)
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrDefault pos
      (toList "BA_DEF_DEF_ " ++ₗ quoteStringLit-chars name ++ₗ
        ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult (mkRawAttrDefault name (RavDecRat d))
              (Trace.pos8 pos name (showDecRat-dec-chars d) outer-suffix)
              outer-suffix)
parseRawAttrDefault-roundtrip-RavDecRatFrac pos name d outer-suffix ss-NL =
  trans (cong (parseRawAttrDefault pos)
              (sym (bridge-RavwFrac name d outer-suffix)))
    (parseRawAttrDefault-format-roundtrip-raw pos name (RavwFrac d)
       outer-suffix ss-NL (ravwFrac-emit-OK d outer-suffix))

-- RavDecRat (bare-int form, fromℤ z): emit `showInt-chars z`.  Wire form
-- goes through `RavwBareInt (mkIntDecRatFromℤ z)` which lifts to
-- `RavDecRat (IntDecRat.value (mkIntDecRatFromℤ z))` ≡ `RavDecRat (fromℤ z)`
-- by definitional reduction of `mkIntDecRatFromℤ`.
parseRawAttrDefault-roundtrip-RavDecRatBareInt :
  ∀ pos (name : List Char) (z : ℤ) (outer-suffix : List Char)
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrDefault pos
      (toList "BA_DEF_DEF_ " ++ₗ quoteStringLit-chars name ++ₗ
        ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult (mkRawAttrDefault name (RavDecRat (fromℤ z)))
              (Trace.pos8 pos name (showInt-chars z) outer-suffix)
              outer-suffix)
parseRawAttrDefault-roundtrip-RavDecRatBareInt pos name z outer-suffix ss-NL =
  -- For bareInt, the input shape uses `showInt-chars z` directly.  The
  -- bridge needs `showInt-chars z ≡ showInt-chars (intDecRatToℤ z')`
  -- where `z' = mkIntDecRatFromℤ z` — closes by
  -- `intDecRatToℤ-mkIntDecRatFromℤ z`.
  trans (cong (parseRawAttrDefault pos) reshape-input)
    (trans (parseRawAttrDefault-format-roundtrip-raw pos name (RavwBareInt z')
              outer-suffix ss-NL (ravwBareInt-emit-OK z' outer-suffix))
      result-eq)
  where
    z' : IntDecRat
    z' = mkIntDecRatFromℤ z

    showInt-eq : showInt-chars (intDecRatToℤ z') ≡ showInt-chars z
    showInt-eq = cong showInt-chars (intDecRatToℤ-mkIntDecRatFromℤ z)

    -- The dispatcher's input shape uses `showInt-chars z`; bridge through
    -- the wire form `showInt-chars (intDecRatToℤ z')`.  Both are equal
    -- via `showInt-eq`, so the input bridge is just `cong` applied to
    -- the shape.
    reshape-input :
      toList "BA_DEF_DEF_ " ++ₗ quoteStringLit-chars name ++ₗ
        ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix
      ≡ emit attrDefaultFmt (name , RavwBareInt z' , tt) ++ₗ outer-suffix
    reshape-input =
      trans (cong (λ chars →
              toList "BA_DEF_DEF_ " ++ₗ quoteStringLit-chars name ++ₗ
                ' ' ∷ chars ++ₗ toList ";\n" ++ₗ outer-suffix)
              (sym showInt-eq))
        (sym (bridge-RavwBareInt name z' outer-suffix))

    -- Result: `IntDecRat.value z' ≡ fromℤ z` is `refl` by definition of
    -- `mkIntDecRatFromℤ`, which sets `IntDecRat.value = fromℤ z`.  The
    -- end-position bridges by structural reduction — `advancePositions
    -- pos (emit attrDefaultFmt (name, RavwBareInt z', tt))` equals
    -- `Trace.pos8 pos name (showInt-chars z) outer-suffix` after the
    -- `showInt-chars (intDecRatToℤ z') ≡ showInt-chars z` rewrite.
    result-eq :
      just (mkResult (mkRawAttrDefault name (liftRavw (RavwBareInt z')))
              (advancePositions pos
                (emit attrDefaultFmt (name , RavwBareInt z' , tt)))
              outer-suffix)
      ≡ just (mkResult (mkRawAttrDefault name (RavDecRat (fromℤ z)))
              (Trace.pos8 pos name (showInt-chars z) outer-suffix)
              outer-suffix)
    result-eq = cong₂ (λ rav fp →
                        just (mkResult (mkRawAttrDefault name rav)
                                       fp outer-suffix))
                       value-eq pos-eq
      where
        -- liftRavw (RavwBareInt z') = RavDecRat (IntDecRat.value z')
        --                           = RavDecRat (fromℤ z)  [definitional]
        value-eq : liftRavw (RavwBareInt z') ≡ RavDecRat (fromℤ z)
        value-eq = refl

        -- end-pos = advancePositions pos (emit attrDefaultFmt
        --   (name, RavwBareInt z', tt)).  Trace.pos8 inlines the same
        --   chars but uses showInt-chars z (not showInt-chars
        --   (intDecRatToℤ z')).  Bridge via `showInt-eq`.
        pos-eq : advancePositions pos
                   (emit attrDefaultFmt (name , RavwBareInt z' , tt))
               ≡ Trace.pos8 pos name (showInt-chars z) outer-suffix
        pos-eq = cong (advancePositions pos)
          (cong (λ chars →
            toList "BA_DEF_DEF_ " ++ₗ quoteStringLit-chars name ++ₗ
              ' ' ∷ chars ++ₗ ';' ∷ '\n' ∷ [])
            showInt-eq)
