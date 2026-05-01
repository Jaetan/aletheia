{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.5.d 3c-B — `parseRawAttrAssign` × ATgtNetwork
-- per-line construct roundtrips (3 emit shapes), η-style migration onto
-- the universal `parseAttrAssign-format-roundtrip` lemma.
--
-- ATgtNetwork is the `RatwNet` constructor of `RawAttrTargetWire`,
-- emitting `[]` (no keyword body).  The Format DSL routes RatwNet through
-- the empty arm (`literal []`) of `stdTargetWireFmt`'s 5-way altSum.  The
-- altSum's `inj₂` disjointness witness needs `parse <4-keyword-chain>
-- pos (value-emit ++ ;\n+os) ≡ nothing` — for closed-Char value heads
-- ('"' / digit / '-') this reduces by `refl` after `parseCharsSeq`'s
-- first-char mismatch fires.
--
-- TraceNetwork module preserved for `Properties/Attributes/Line.agda`'s
-- per-target-shape line dispatchers.

module Aletheia.DBC.TextParser.Properties.Attributes.Assign.Network where

open import Data.Bool using (Bool; true; false; T)
open import Data.Char using (Char)
open import Data.Char.Base using (_≈ᵇ_; isDigit)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_; length) renaming (_++_ to _++ₗ_)
open import Data.List.Properties using () renaming (++-assoc to ++ₗ-assoc; length-++ to length-++ₗ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃₂; _,_; Σ; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String; toList)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; _≢_)

open import Aletheia.Parser.Combinators
  using (Position; Parser; ParseResult; mkResult; advancePosition; advancePositions;
         _>>=_; pure; _<|>_; _*>_; _<*_; string;
         char; many; satisfy; fail)
open import Aletheia.DBC.DecRat using (DecRat; mkDecRat; IsCanonical; fromℤ)
open import Aletheia.DBC.DecRat.Refinement using
  (IntDecRat; mkIntDecRatFromℤ; intDecRatToℤ;
   intDecRatToℤ-mkIntDecRatFromℤ)
open import Aletheia.DBC.Types using
  ( AttrTarget; ATgtNetwork; ATgtNode; ATgtMessage; ATgtSignal; ATgtEnvVar
  ; ATgtNodeMsg; ATgtNodeSig)
open import Aletheia.DBC.Identifier using (Identifier)

open import Aletheia.DBC.TextParser.Attributes
  using (parseRawAttrAssign;
         RawAttrAssign; mkRawAttrAssign;
         RawAttrValue; RavString; RavDecRat;
         liftRavw; buildAttrAssignP)
open import Aletheia.DBC.TextParser.Lexer
  using (parseWS; parseWSOpt; parseStringLit; parseNewline;
         isHSpace)

open import Aletheia.DBC.TextFormatter.Emitter
  using (quoteStringLit-chars; showDecRat-dec-chars; showInt-chars;
         showNat-chars; digitChar)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  ( bind-just-step
  ; SuffixStops; ∷-stop; []-stop
  ; advancePositions-++
  ; showDecRat-chars-head-digit; showDecRat-chars-head-dash
  ; showNat-chars-head)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  ( isNewlineStart
  ; manyHelper-parseNewline-exhaust)
open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Common using
  ( showInt-chars-head-classify; showDecRat-chars-head-classify
  ; value-stops-isHSpace-RavString
  ; value-stops-isHSpace-RavDecRatFrac
  ; value-stops-isHSpace-RavDecRatBareInt
  ; digitChar-not-quote; digitChar-not-isHSpace
  ; digitChar-not-B; digitChar-not-S; digitChar-not-E)

open import Aletheia.DBC.TextParser.Format using
  (Format; emit; parse; EmitsOK)
open import Aletheia.DBC.TextParser.Format.AttrValue using
  (RawAttrValueWire; RavwString; RavwFrac; RavwBareInt;
   attrValueWireFmt;
   build-EmitsOK-RavwString;
   build-EmitsOK-RavwFrac;
   build-EmitsOK-RavwBareInt)
open import Aletheia.DBC.TextParser.Format.AttrLine using
  (attrAssignFmt; AttrAssignCarrier;
   stdTargetWireFmt; RatwNet;
   parseAttrAssign-format-roundtrip;
   parseAttrAssign-format-roundtrip-RatwNet;
   emit-attrAssignFmt-RatwNet;
   emit-stdTargetWireFmt-RatwNet-on-quote-head;
   emit-stdTargetWireFmt-RatwNet-on-dash-head;
   emit-stdTargetWireFmt-RatwNet-on-digit-head)

-- ============================================================================
-- TRACE MODULE — kept for `Properties/Attributes/Line.agda` compatibility
-- ============================================================================

module TraceNetwork (pos : Position) (name : List Char) (value-chars : List Char)
                    (outer-suffix : List Char) where
  cs-name : List Char
  cs-name = quoteStringLit-chars name

  -- Single advancePositions call over the full inline-line shape.
  -- Mirrors Default.agda's `Trace.pos8` pattern — definitionally equal
  -- to `advancePositions pos (emit attrAssignFmt (name, RatwNet, wireVal,
  -- tt))` after the public `emit-attrAssignFmt-RatwNet` bridge.
  pos9 : Position
  pos9 = advancePositions pos
           (toList "BA_ " ++ₗ cs-name ++ₗ
            ' ' ∷ value-chars ++ₗ ';' ∷ '\n' ∷ [])

-- ============================================================================
-- BRIDGES — emit form ↔ inline-input shape
-- ============================================================================
--
-- Mirror of Default.agda's bridge structure.  Two-step ++-assoc bridge:
--   (qsl(name) ++ ' ' ∷ (value-chars ++ ';' ∷ '\n' ∷ [])) ++ outer-suffix
-- ↔ qsl(name) ++ ' ' ∷ (value-chars ++ ';' ∷ '\n' ∷ outer-suffix)

private
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

  -- Per-shape bridge: emit attrAssignFmt (...) ++ outer ≡ inline-input.
  -- Uses the public `emit-attrAssignFmt-RatwNet` lemma to lift the deep
  -- iso/pair structure to a flat closed-Char + qsl ++ ' ' ∷ value form,
  -- then ++ₗ-assoc bridges the trailing `;\n` slot.
  bridge-Network-emit :
    ∀ (name : List Char) (wireVal : RawAttrValueWire) (outer-suffix : List Char)
    → emit attrAssignFmt (name , RatwNet , wireVal , tt) ++ₗ outer-suffix
      ≡ 'B' ∷ 'A' ∷ '_' ∷ ' ' ∷ quoteStringLit-chars name ++ₗ
          ' ' ∷ (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)
  bridge-Network-emit name wireVal outer-suffix =
    trans
      (cong (_++ₗ outer-suffix)
            (emit-attrAssignFmt-RatwNet name wireVal))
      (cong (λ z → 'B' ∷ 'A' ∷ '_' ∷ ' ' ∷ z)
            (bridge-tail name (emit attrValueWireFmt wireVal) outer-suffix))

-- ============================================================================
-- COMMON RAW-LEVEL ROUNDTRIP — Network arm
-- ============================================================================

-- B.3.d 3d.5.d 3c-B Path 1 — RatwNet helper now uses the specialized
-- `parseAttrAssign-format-roundtrip-RatwNet` (head-class witness) rather
-- than the universal lemma + EmitsOK obligation.  See
-- `feedback_emitsok_inj2_deep_pattern.md` for the rationale: the
-- universal-lemma path's L5 (`EmitsOK stdTargetWireFmt RatwNet …`) blows
-- -M16G at the inj₂-deep altSum position with abstract input.  The head
-- witness (head Char + 3 inequalities `(x ≈ᵇ 'B') ≡ false`, `'S'`, `'E'`)
-- is small and locally derivable in the per-shape dispatchers.
private
  parseRawAttrAssign-format-roundtrip-Network-raw :
    ∀ (pos : Position) (name : List Char) (wireVal : RawAttrValueWire)
      (outer-suffix : List Char)
      (x : Char) (tail : List Char)
    → SuffixStops isNewlineStart outer-suffix
    → SuffixStops isHSpace
        (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)
    → EmitsOK attrValueWireFmt wireVal (';' ∷ '\n' ∷ outer-suffix)
    → emit attrValueWireFmt wireVal ≡ x ∷ tail
    → (x Data.Char.Base.≈ᵇ 'B') ≡ false
    → (x Data.Char.Base.≈ᵇ 'S') ≡ false
    → (x Data.Char.Base.≈ᵇ 'E') ≡ false
    → parseRawAttrAssign pos
        (emit attrAssignFmt (name , RatwNet , wireVal , tt) ++ₗ outer-suffix)
      ≡ just (mkResult (mkRawAttrAssign name ATgtNetwork (liftRavw wireVal))
                (advancePositions pos
                  (emit attrAssignFmt (name , RatwNet , wireVal , tt)))
                outer-suffix)
  parseRawAttrAssign-format-roundtrip-Network-raw pos name wireVal outer-suffix
                                                  x tail ss-NL l4 l6
                                                  val-eq x≢B x≢S x≢E =
    trans step-format
      (trans step-many-newline step-buildP)
    where
      pos-line : Position
      pos-line = advancePositions pos
                   (emit attrAssignFmt (name , RatwNet , wireVal , tt))

      cont-line : AttrAssignCarrier → Parser RawAttrAssign
      cont-line c = many parseNewline >>= λ _ →
                    buildAttrAssignP (proj₁ c)
                                     (proj₁ (proj₂ c))
                                     (proj₁ (proj₂ (proj₂ c)))

      cont-blanks : List Char → Parser RawAttrAssign
      cont-blanks _ = buildAttrAssignP name RatwNet wireVal

      step-format :
        parseRawAttrAssign pos
          (emit attrAssignFmt (name , RatwNet , wireVal , tt) ++ₗ outer-suffix)
        ≡ cont-line (name , RatwNet , wireVal , tt) pos-line outer-suffix
      step-format =
        bind-just-step (parse attrAssignFmt) cont-line
          pos
          (emit attrAssignFmt (name , RatwNet , wireVal , tt) ++ₗ outer-suffix)
          (name , RatwNet , wireVal , tt) pos-line outer-suffix
          (parseAttrAssign-format-roundtrip-RatwNet pos name wireVal
            outer-suffix x tail l4 l6 val-eq x≢B x≢S x≢E)

      step-many-newline :
        cont-line (name , RatwNet , wireVal , tt) pos-line outer-suffix
        ≡ cont-blanks [] pos-line outer-suffix
      step-many-newline =
        bind-just-step (many parseNewline) cont-blanks
          pos-line outer-suffix
          [] pos-line outer-suffix
          (manyHelper-parseNewline-exhaust pos-line outer-suffix
            (length outer-suffix) ss-NL)

      step-buildP :
        cont-blanks [] pos-line outer-suffix
        ≡ just (mkResult (mkRawAttrAssign name ATgtNetwork (liftRavw wireVal))
                  pos-line outer-suffix)
      step-buildP = refl

-- ============================================================================
-- Top-level dispatcher: ATgtNetwork × RavString
-- ============================================================================

parseRawAttrAssign-roundtrip-ATgtNetwork-RavString :
  ∀ pos (name : List Char) (s : List Char) (outer-suffix : List Char)
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrAssign pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name ATgtNetwork (RavString s))
              (TraceNetwork.pos9 pos name (quoteStringLit-chars s) outer-suffix)
              outer-suffix)
parseRawAttrAssign-roundtrip-ATgtNetwork-RavString pos name s outer-suffix ss-NL =
  trans
    (cong (parseRawAttrAssign pos) (sym (bridge-Network-emit name (RavwString s) outer-suffix)))
    (trans
      (parseRawAttrAssign-format-roundtrip-Network-raw pos name
        (RavwString s) outer-suffix _ _ ss-NL l4 l6 refl refl refl refl)
      result-eq)
  where
    l4 : SuffixStops isHSpace
           (emit attrValueWireFmt (RavwString s) ++ₗ ';' ∷ '\n' ∷ outer-suffix)
    l4 = value-stops-isHSpace-RavString s outer-suffix

    l6 : EmitsOK attrValueWireFmt (RavwString s) (';' ∷ '\n' ∷ outer-suffix)
    l6 = build-EmitsOK-RavwString s (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl)

    result-eq :
      just (mkResult (mkRawAttrAssign name ATgtNetwork
                       (liftRavw (RavwString s)))
              (advancePositions pos
                (emit attrAssignFmt (name , RatwNet , RavwString s , tt)))
              outer-suffix)
      ≡ just (mkResult
                (mkRawAttrAssign name ATgtNetwork (RavString s))
                (TraceNetwork.pos9 pos name (quoteStringLit-chars s) outer-suffix)
                outer-suffix)
    result-eq = cong (λ p → just (mkResult
                                    (mkRawAttrAssign name ATgtNetwork (RavString s))
                                    p outer-suffix))
                     (cong (advancePositions pos)
                           (emit-attrAssignFmt-RatwNet name (RavwString s)))

-- ============================================================================
-- L5 DISJOINTNESS — sourced from Format/AttrLine.agda
-- ============================================================================
--
-- The L5 obligation of `parseAttrAssign-format-roundtrip` for `RatwNet`
-- reduces to `⊤ × (∀ pos → parse <left-keyword-chain> pos input ≡ nothing)`.
-- The keyword chain is private to Format/AttrLine.agda — so the public
-- `emit-stdTargetWireFmt-RatwNet-on-{quote,dash,digit}-head` helpers
-- (defined where left-chain is in scope) take an `input ≡ <head> ∷ tail`
-- equality and pattern-match `refl` to expose the closed head locally,
-- closing the disjointness without `subst` over the (huge) `EmitsOK …`
-- predicate.  Caller dispatches on `showDecRat-chars-head-classify` /
-- `showInt-chars-head-classify` and forwards the head-eq.
--
-- The dispatcher's input shape `showXxx-chars w ++ rest` is bridged to
-- `<head> ∷ tail ++ rest` via `cong (_++ₗ rest)` on the head-classify eq —
-- a small `cong`, not a `subst` over the EmitsOK predicate.

-- ============================================================================
-- ATgtNetwork × RavDecRat-frac dispatcher
-- ============================================================================
--
-- B.3.d 3d.5.d 3c-B Path 1: dispatch on `showDecRat-chars-head-classify`'s
-- digit-or-dash sum, deriving the 3 keyword inequalities (x ≢ 'B' / 'S'
-- / 'E') for each head class.  Calls the head-witness-aware helper.

-- B.3.d 3d.5.d 3c-B Path 1 — hoisted per-shape helpers.  See
-- `feedback_with_abstraction_traps.md` rule #2 + advisor diagnosis
-- 2026-05-01: when each `with`-arm of the Frac/BareInt dispatchers had
-- its own where-block defining `l4`/`l6`/`result-eq`/etc., Agda type-
-- checked each duplicate separately, forcing per-arm reduction of
-- `EmitsOK attrValueWireFmt (Ravw{Frac,BareInt} _) ...` over abstract
-- d/z (inj₂-position altSum element → 9-deep `Σ × Π` chain).  Doubling
-- the work blew -M16G.  Module-level helpers type-check once.

private
  l4-RavwFrac : ∀ (d : DecRat) (outer-suffix : List Char) →
    SuffixStops isHSpace
      (emit attrValueWireFmt (RavwFrac d) ++ₗ ';' ∷ '\n' ∷ outer-suffix)
  l4-RavwFrac d outer-suffix = value-stops-isHSpace-RavDecRatFrac d outer-suffix

  l6-RavwFrac : ∀ (d : DecRat) (outer-suffix : List Char) →
    EmitsOK attrValueWireFmt (RavwFrac d) (';' ∷ '\n' ∷ outer-suffix)
  l6-RavwFrac d outer-suffix =
    build-EmitsOK-RavwFrac d (';' ∷ '\n' ∷ outer-suffix) (∷-stop refl)

  result-eq-Frac :
    ∀ pos (name : List Char) (d : DecRat) (outer-suffix : List Char) →
    just (mkResult (mkRawAttrAssign name ATgtNetwork
                     (liftRavw (RavwFrac d)))
            (advancePositions pos
              (emit attrAssignFmt (name , RatwNet , RavwFrac d , tt)))
            outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name ATgtNetwork (RavDecRat d))
              (TraceNetwork.pos9 pos name (showDecRat-dec-chars d) outer-suffix)
              outer-suffix)
  result-eq-Frac pos name d outer-suffix =
    cong (λ p → just (mkResult
                        (mkRawAttrAssign name ATgtNetwork (RavDecRat d))
                        p outer-suffix))
         (cong (advancePositions pos)
               (emit-attrAssignFmt-RatwNet name (RavwFrac d)))

-- B.3.d 3d.5.d 3c-B Path 1 — Frac dispatcher refactored to constructor
-- pattern-match + projection-based head-witness extraction.  See
-- `feedback_with_abstraction_traps.md` rule #2 + advisor diagnosis 2026-05-01.
-- The original `with showDecRat-chars-head-classify d` over abstract DecRat
-- triggered goal-rebuild thrashing on the wide ∃₂ × _⊎_ result type at
-- inj₂-deep value position of attrValueWireFmt's altSum, blowing -M16G.
-- Pattern-matching on `mkDecRat`'s 3 numerator constructors + projecting
-- the head witness from `showDecRat-chars-head-digit` / `-dash` (no `with`)
-- eliminates the goal-rebuild cycle.
parseRawAttrAssign-roundtrip-ATgtNetwork-RavDecRatFrac :
  ∀ pos (name : List Char) (d : DecRat) (outer-suffix : List Char)
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrAssign pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name ATgtNetwork (RavDecRat d))
              (TraceNetwork.pos9 pos name (showDecRat-dec-chars d) outer-suffix)
              outer-suffix)
parseRawAttrAssign-roundtrip-ATgtNetwork-RavDecRatFrac pos name
  (mkDecRat (+ zero) a b cx) outer-suffix ss-NL =
  let d-this = mkDecRat (+ zero) a b cx
      classify = showDecRat-chars-head-digit zero a b cx
      k = proj₁ classify
      subtail = proj₁ (proj₂ classify)
      k<10 = proj₁ (proj₂ (proj₂ classify))
      eq = proj₂ (proj₂ (proj₂ classify))
  in trans
    (cong (parseRawAttrAssign pos)
          (sym (bridge-Network-emit name (RavwFrac d-this) outer-suffix)))
    (trans
      (parseRawAttrAssign-format-roundtrip-Network-raw pos name
        (RavwFrac d-this) outer-suffix
        (digitChar k) subtail ss-NL
        (l4-RavwFrac d-this outer-suffix)
        (l6-RavwFrac d-this outer-suffix)
        eq
        (digitChar-not-B k k<10)
        (digitChar-not-S k k<10)
        (digitChar-not-E k k<10))
      (result-eq-Frac pos name d-this outer-suffix))
parseRawAttrAssign-roundtrip-ATgtNetwork-RavDecRatFrac pos name
  (mkDecRat (+ suc n) a b cx) outer-suffix ss-NL =
  let d-this = mkDecRat (+ suc n) a b cx
      classify = showDecRat-chars-head-digit (suc n) a b cx
      k = proj₁ classify
      subtail = proj₁ (proj₂ classify)
      k<10 = proj₁ (proj₂ (proj₂ classify))
      eq = proj₂ (proj₂ (proj₂ classify))
  in trans
    (cong (parseRawAttrAssign pos)
          (sym (bridge-Network-emit name (RavwFrac d-this) outer-suffix)))
    (trans
      (parseRawAttrAssign-format-roundtrip-Network-raw pos name
        (RavwFrac d-this) outer-suffix
        (digitChar k) subtail ss-NL
        (l4-RavwFrac d-this outer-suffix)
        (l6-RavwFrac d-this outer-suffix)
        eq
        (digitChar-not-B k k<10)
        (digitChar-not-S k k<10)
        (digitChar-not-E k k<10))
      (result-eq-Frac pos name d-this outer-suffix))
parseRawAttrAssign-roundtrip-ATgtNetwork-RavDecRatFrac pos name
  (mkDecRat -[1+ n ] a b cx) outer-suffix ss-NL =
  let d-this = mkDecRat -[1+ n ] a b cx
      dash-witness = showDecRat-chars-head-dash n a b cx
      subtail = proj₁ dash-witness
      eq = proj₂ dash-witness
  in trans
    (cong (parseRawAttrAssign pos)
          (sym (bridge-Network-emit name (RavwFrac d-this) outer-suffix)))
    (trans
      (parseRawAttrAssign-format-roundtrip-Network-raw pos name
        (RavwFrac d-this) outer-suffix
        '-' subtail ss-NL
        (l4-RavwFrac d-this outer-suffix)
        (l6-RavwFrac d-this outer-suffix)
        eq
        refl refl refl)
      (result-eq-Frac pos name d-this outer-suffix))

-- ============================================================================
-- ATgtNetwork × RavDecRat-bareInt dispatcher
-- ============================================================================

private
  -- Hoisted helpers (mirror of the Frac block above).  See note before the
  -- Frac dispatcher's `private` block — module-level helpers type-check once,
  -- avoiding the per-`with`-arm duplication that blows -M16G.
  showInt-eq-BareInt : ∀ (z : ℤ) →
    showInt-chars (intDecRatToℤ (mkIntDecRatFromℤ z)) ≡ showInt-chars z
  showInt-eq-BareInt z = cong showInt-chars (intDecRatToℤ-mkIntDecRatFromℤ z)

  reshape-input-BareInt :
    ∀ (name : List Char) (z : ℤ) (outer-suffix : List Char) →
    toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
      ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix
    ≡ emit attrAssignFmt (name , RatwNet , RavwBareInt (mkIntDecRatFromℤ z) , tt)
        ++ₗ outer-suffix
  reshape-input-BareInt name z outer-suffix =
    trans (cong (λ chars →
            toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
              ' ' ∷ chars ++ₗ toList ";\n" ++ₗ outer-suffix)
            (sym (showInt-eq-BareInt z)))
      (sym (bridge-Network-emit name (RavwBareInt (mkIntDecRatFromℤ z)) outer-suffix))

  l4-RavwBareInt : ∀ (z : ℤ) (outer-suffix : List Char) →
    SuffixStops isHSpace
      (emit attrValueWireFmt (RavwBareInt (mkIntDecRatFromℤ z))
        ++ₗ ';' ∷ '\n' ∷ outer-suffix)
  l4-RavwBareInt z outer-suffix =
    subst (λ chars → SuffixStops isHSpace (chars ++ₗ ';' ∷ '\n' ∷ outer-suffix))
          (sym (showInt-eq-BareInt z))
          (value-stops-isHSpace-RavDecRatBareInt z outer-suffix)

  l6-RavwBareInt : ∀ (z : ℤ) (outer-suffix : List Char) →
    EmitsOK attrValueWireFmt (RavwBareInt (mkIntDecRatFromℤ z))
      (';' ∷ '\n' ∷ outer-suffix)
  l6-RavwBareInt z outer-suffix =
    build-EmitsOK-RavwBareInt (mkIntDecRatFromℤ z) (';' ∷ '\n' ∷ outer-suffix)
                              (∷-stop refl) (λ ())

  result-eq-BareInt :
    ∀ pos (name : List Char) (z : ℤ) (outer-suffix : List Char) →
    just (mkResult (mkRawAttrAssign name ATgtNetwork
                     (liftRavw (RavwBareInt (mkIntDecRatFromℤ z))))
            (advancePositions pos
              (emit attrAssignFmt
                (name , RatwNet , RavwBareInt (mkIntDecRatFromℤ z) , tt)))
            outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name ATgtNetwork (RavDecRat (fromℤ z)))
              (TraceNetwork.pos9 pos name (showInt-chars z) outer-suffix)
              outer-suffix)
  result-eq-BareInt pos name z outer-suffix =
    cong₂ (λ rav fp → just (mkResult (mkRawAttrAssign name ATgtNetwork rav)
                                     fp outer-suffix))
          refl
          (cong (advancePositions pos)
                 (trans (emit-attrAssignFmt-RatwNet name
                          (RavwBareInt (mkIntDecRatFromℤ z)))
                        (cong (λ chars →
                                toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
                                  ' ' ∷ chars ++ₗ ';' ∷ '\n' ∷ [])
                              (showInt-eq-BareInt z))))

-- B.3.d 3d.5.d 3c-B Path 1 — BareInt dispatcher refactored to constructor
-- pattern-match on `z : ℤ` + projection-based head-witness extraction
-- (mirror of Frac's refactor, same rationale).  For `z = + n`, head is
-- digit `digitChar k` derived from `showNat-chars-head n` (since
-- `showInt-chars (+ n) = showNat-chars n` and the lemma
-- `intDecRatToℤ-mkIntDecRatFromℤ z` lets us bridge from `showInt-chars
-- (intDecRatToℤ z') = showInt-chars z`).  For `z = -[1+ n ]`, head is
-- closed `'-'`.
parseRawAttrAssign-roundtrip-ATgtNetwork-RavDecRatBareInt :
  ∀ pos (name : List Char) (z : ℤ) (outer-suffix : List Char)
  → SuffixStops isNewlineStart outer-suffix
  → parseRawAttrAssign pos
      (toList "BA_ " ++ₗ quoteStringLit-chars name ++ₗ
        ' ' ∷ showInt-chars z ++ₗ toList ";\n" ++ₗ outer-suffix)
    ≡ just (mkResult
              (mkRawAttrAssign name ATgtNetwork (RavDecRat (fromℤ z)))
              (TraceNetwork.pos9 pos name (showInt-chars z) outer-suffix)
              outer-suffix)
parseRawAttrAssign-roundtrip-ATgtNetwork-RavDecRatBareInt pos name (+ n) outer-suffix ss-NL =
  let nat-witness = showNat-chars-head n
      k = proj₁ nat-witness
      subtail = proj₁ (proj₂ nat-witness)
      k<10 = proj₁ (proj₂ (proj₂ nat-witness))
      nat-eq = proj₂ (proj₂ (proj₂ nat-witness))
      -- bridge from `showNat-chars n ≡ digitChar k ∷ subtail` to
      -- `emit attrValueWireFmt (RavwBareInt (mkIntDecRatFromℤ (+ n)))
      --   ≡ digitChar k ∷ subtail`.
      val-eq = trans (showInt-eq-BareInt (+ n)) nat-eq
  in trans
    (cong (parseRawAttrAssign pos) (reshape-input-BareInt name (+ n) outer-suffix))
    (trans
      (parseRawAttrAssign-format-roundtrip-Network-raw pos name
        (RavwBareInt (mkIntDecRatFromℤ (+ n))) outer-suffix
        (digitChar k) subtail ss-NL
        (l4-RavwBareInt (+ n) outer-suffix)
        (l6-RavwBareInt (+ n) outer-suffix)
        val-eq
        (digitChar-not-B k k<10)
        (digitChar-not-S k k<10)
        (digitChar-not-E k k<10))
      (result-eq-BareInt pos name (+ n) outer-suffix))
parseRawAttrAssign-roundtrip-ATgtNetwork-RavDecRatBareInt pos name -[1+ n ] outer-suffix ss-NL =
  -- For `-[1+ n ]`, `showInt-chars` emits `'-' ∷ showNat-chars (suc n)`
  -- so `showInt-chars-eq` is `'-' ∷ showNat-chars (suc n) ≡ '-' ∷ rest`,
  -- closed dash head.
  let val-eq = showInt-eq-BareInt -[1+ n ]
  in trans
    (cong (parseRawAttrAssign pos) (reshape-input-BareInt name -[1+ n ] outer-suffix))
    (trans
      (parseRawAttrAssign-format-roundtrip-Network-raw pos name
        (RavwBareInt (mkIntDecRatFromℤ -[1+ n ])) outer-suffix
        '-' (showNat-chars (suc n)) ss-NL
        (l4-RavwBareInt -[1+ n ] outer-suffix)
        (l6-RavwBareInt -[1+ n ] outer-suffix)
        val-eq
        refl refl refl)
      (result-eq-BareInt pos name -[1+ n ] outer-suffix))
