{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.5.d 3c-B — DSL-side Format for the BA_DEF_DEF_ / BA_ /
-- BA_REL_ attribute-value slot.
--
-- The wire grammar at the value slot is 3-emit-shape:
--   * `RavwString cs`   — emit `quoteStringLit-chars cs`     (AVString)
--   * `RavwFrac    d`   — emit `showDecRat-dec-chars d`      (AVFloat)
--   * `RavwBareInt z`   — emit `showInt-chars (intDecRatToℤ z)` (AVInt /
--                                                       AVEnum / AVHex)
--
-- Even though the public `RawAttrValue` ADT in `TextParser/Attributes.agda`
-- collapses these into 2 ctors (RavString / RavDecRat), the wire-form ADT
-- here keeps the emit-shape distinction so the Format DSL can route each
-- shape through its own typed leaf (`stringLit` / `decRatFrac` /
-- `intDecRat`).  A `liftRavw : RawAttrValueWire → RawAttrValue` projection
-- lifts the wire form back to the public ADT — both DecRat-bearing wire
-- ctors collapse to `RavDecRat` (frac uses the carried DecRat directly,
-- bareInt projects via `IntDecRat.value`).
--
-- The 3-way `altSum stringLit (altSum decRatFrac intDecRat)` works
-- because:
--   * `decRatFrac` parser is `parseDecRatFrac` — REQUIRES a `.` — so it
--     fails on bare-int input ("42") and the altSum falls through to
--     `intDecRat`'s arm.  Reverse ordering would break: `parseIntDecRat`
--     parses "1.0" as IntDecRat 1 (parseDecRat handles the frac form,
--     then refinement isInteger 1 succeeds), so `intDecRat` would
--     incorrectly capture frac-form integer-valued AVFloat values.
--   * `stringLit` head is `'"'` — disjoint from digit/'-' heads of
--     decRatFrac/intDecRat emit, so the outer altSum disjointness closes
--     by closed-Char comparison.
--
-- Universal `parseRawAttrValueWire-format-roundtrip` follows from a
-- single `roundtrip attrValueWireFmt` call backed by a per-shape EmitsOK
-- builder.  Per-shape dispatchers in `Properties/Attributes/Default.agda`
-- (3 cases) and `Properties/Attributes/Assign/*.agda` (5 std × 3 + 2 rel
-- × 3 = 21 cases) collapse from per-shape bind-chain reasoning to slim
-- wrappers around this lemma.

module Aletheia.DBC.TextParser.Format.AttrValue where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char; _≈ᵇ_)
open import Data.Char.Base using (isDigit)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; subst)

open import Aletheia.Parser.Combinators
  using (Position; Parser; mkResult; advancePositions)
open import Aletheia.DBC.DecRat using (DecRat; mkDecRat)
open import Aletheia.DBC.DecRat.Refinement using
  (IntDecRat; intDecRatToℤ; mkIntDecRatFromℤ;
   NatDecRat; natDecRatToℕ; natDecRatToIntDecRat)
open import Aletheia.DBC.TextParser.Lexer using (isHSpace)
open import Aletheia.DBC.TextFormatter.Emitter using
  (digitChar; showInt-chars; showNat-chars; showDecRat-dec-chars;
   quoteStringLit-chars)
open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; ∷-stop; headOr;
   showNat-chars-head;
   showDecRat-chars-head-dash; showDecRat-chars-head-digit)
open import Aletheia.DBC.TextParser.Format using
  (Format; literal; ident; nat; stringLit; pair; iso; many;
   altSum; ws; wsOpt; wsCanonOne; decRat; decRatFrac;
   intDecRat; natDecRat; withPrefix;
   emit; parse; EmitsOK; ParseFailsAt; roundtrip)

-- ============================================================================
-- WIRE-FORM ADT (3-emit-shape)
-- ============================================================================

data RawAttrValueWire : Set where
  RavwString  : List Char → RawAttrValueWire
  RavwFrac    : DecRat    → RawAttrValueWire
  RavwBareInt : IntDecRat → RawAttrValueWire

-- ============================================================================
-- FORMAT DSL ASSEMBLY — 3-way altSum (decRatFrac FIRST)
-- ============================================================================

private
  AttrValueWireCarrier : Set
  AttrValueWireCarrier = List Char ⊎ (DecRat ⊎ IntDecRat)

  attrValueWireCarrierFmt : Format AttrValueWireCarrier
  attrValueWireCarrierFmt =
    altSum stringLit (altSum decRatFrac intDecRat)

  fwdRavw : AttrValueWireCarrier → RawAttrValueWire
  fwdRavw (inj₁ s)        = RavwString s
  fwdRavw (inj₂ (inj₁ d)) = RavwFrac d
  fwdRavw (inj₂ (inj₂ z)) = RavwBareInt z

  bwdRavw : RawAttrValueWire → AttrValueWireCarrier
  bwdRavw (RavwString s)  = inj₁ s
  bwdRavw (RavwFrac d)    = inj₂ (inj₁ d)
  bwdRavw (RavwBareInt z) = inj₂ (inj₂ z)

  fwdRavw-bwdRavw : ∀ rv → fwdRavw (bwdRavw rv) ≡ rv
  fwdRavw-bwdRavw (RavwString _)  = refl
  fwdRavw-bwdRavw (RavwFrac _)    = refl
  fwdRavw-bwdRavw (RavwBareInt _) = refl

attrValueWireFmt : Format RawAttrValueWire
attrValueWireFmt =
  iso fwdRavw bwdRavw fwdRavw-bwdRavw attrValueWireCarrierFmt

-- ============================================================================
-- HEAD-CHAR HELPERS — closed-char head non-quote / non-hspace dispatches
-- ============================================================================
--
-- For the altSum disjointness witnesses we need to show the head of the
-- alt's first arm fails on the alt's second arm's emit input.  Two
-- specialisations are needed:
--   * `parse stringLit fail` on input starting with digit/'-' — straight
--     closed-Char ≈ᵇ '"' = false.
--   * `parse decRatFrac fail` on input starting with digit/'-' but with
--     no '.' before the next non-digit — `parseDecRatFrac` requires '.',
--     so it fails after consuming the digits if the next char isn't '.'.
--
-- `showInt-chars-head-stop` and `showDecRat-chars-head-stop` are public
-- so `Format/AttrLine.agda` can use them for the leading-ws witness on
-- `RavwBareInt`/`RavwFrac` shapes.  `digit-not-isHSpace` is public for
-- the same reason (needed by per-shape leading-ws witnesses).

-- 10 digit chars are non-hspace.  Mirror of `Format/AttrDef.agda`'s helper.
digit-not-isHSpace : ∀ d → isHSpace (digitChar d) ≡ false
digit-not-isHSpace 0 = refl
digit-not-isHSpace 1 = refl
digit-not-isHSpace 2 = refl
digit-not-isHSpace 3 = refl
digit-not-isHSpace 4 = refl
digit-not-isHSpace 5 = refl
digit-not-isHSpace 6 = refl
digit-not-isHSpace 7 = refl
digit-not-isHSpace 8 = refl
digit-not-isHSpace 9 = refl
digit-not-isHSpace
  (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) = refl

-- Head of `(showInt-chars z ++ inner-rest) ++ outer-suffix` is non-hspace.
-- Three-case dispatch: `(+ zero)` / `(+ suc n)` / `-[1+ _ ]`.
showInt-chars-head-stop : ∀ (z : ℤ) (rest : List Char)
  → SuffixStops isHSpace (showInt-chars z ++ₗ rest)
showInt-chars-head-stop (+ n) rest with showNat-chars-head n
... | d , tail , _ , eq =
      subst (λ xs → SuffixStops isHSpace (xs ++ₗ rest))
            (sym eq)
            (∷-stop (digit-not-isHSpace d))
showInt-chars-head-stop (-[1+ _ ]) _ = ∷-stop refl

-- Head of `(showDecRat-dec-chars d ++ inner-rest) ++ outer-suffix` is
-- non-hspace.  Three-case dispatch on the DecRat numerator's sign.
showDecRat-chars-head-stop : ∀ (d : DecRat) (rest : List Char)
  → SuffixStops isHSpace (showDecRat-dec-chars d ++ₗ rest)
showDecRat-chars-head-stop (mkDecRat (+ zero) a b cx) rest
  with showDecRat-chars-head-digit zero a b cx
... | k , tail , _ , eq =
      subst (λ xs → SuffixStops isHSpace (xs ++ₗ rest))
            (sym eq)
            (∷-stop (digit-not-isHSpace k))
showDecRat-chars-head-stop (mkDecRat (+ suc n) a b cx) rest
  with showDecRat-chars-head-digit (suc n) a b cx
... | k , tail , _ , eq =
      subst (λ xs → SuffixStops isHSpace (xs ++ₗ rest))
            (sym eq)
            (∷-stop (digit-not-isHSpace k))
showDecRat-chars-head-stop (mkDecRat (-[1+ n ]) a b cx) rest
  with showDecRat-chars-head-dash n a b cx
... | tail , eq =
      subst (λ xs → SuffixStops isHSpace (xs ++ₗ rest))
            (sym eq)
            (∷-stop refl)

-- ============================================================================
-- DISJOINTNESS — parse stringLit fails on numeric emit
-- ============================================================================
--
-- The outer altSum's `inj₂` disjointness requires `parse stringLit pos
-- (numeric-emit ++ suffix) ≡ nothing`.  Closed-Char comparison: numeric
-- emit starts with a digit (0–9) or `'-'` (negative), neither of which
-- equals `'"'`.

private
  -- `parseStringLit` on input with non-quote head fails.  See `parseStringLit-
  -- fail-on-non-quote` in `Properties/Attributes/Default.agda` for the
  -- canonical formulation; replicated here so the bridge proofs don't
  -- need to import Properties.
  parseStringLit-fail-on-non-quote : ∀ pos c rest
    → (c ≈ᵇ '"') ≡ false
    → parse stringLit pos (c ∷ rest) ≡ nothing
  parseStringLit-fail-on-non-quote pos c rest c-eq = body
    where
      open import Aletheia.Parser.Combinators using (char; _>>=_; pure)
        renaming (many to many-parser)
      open import Aletheia.DBC.TextParser.Lexer using (parseStringChar)
      open import Aletheia.DBC.TextParser.Properties.Primitives using (bind-nothing)
      char-fails : char '"' pos (c ∷ rest) ≡ nothing
      char-fails rewrite c-eq = refl
      body : parse stringLit pos (c ∷ rest) ≡ nothing
      body = bind-nothing (char '"')
        (λ _ → many-parser parseStringChar >>= λ chars →
               char '"' >>= λ _ → pure chars)
        pos (c ∷ rest)
        char-fails

  -- digitChar d ≢ '"' for any d.
  digitChar-not-quote : ∀ d → d Data.Nat.< 10 → (digitChar d ≈ᵇ '"') ≡ false
  digitChar-not-quote 0 _ = refl
  digitChar-not-quote 1 _ = refl
  digitChar-not-quote 2 _ = refl
  digitChar-not-quote 3 _ = refl
  digitChar-not-quote 4 _ = refl
  digitChar-not-quote 5 _ = refl
  digitChar-not-quote 6 _ = refl
  digitChar-not-quote 7 _ = refl
  digitChar-not-quote 8 _ = refl
  digitChar-not-quote 9 _ = refl
  digitChar-not-quote (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _))))))))))
    (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s
      (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s ()))))))))))

  -- `parse stringLit pos (showDecRat-dec-chars d ++ suffix) ≡ nothing`.
  parse-stringLit-fail-on-decRat : ∀ pos d suffix
    → parse stringLit pos (showDecRat-dec-chars d ++ₗ suffix) ≡ nothing
  parse-stringLit-fail-on-decRat pos (mkDecRat (+ zero) a b cx) suffix
    with showDecRat-chars-head-digit zero a b cx
  ... | k , tail , k<10 , eq =
        subst (λ chars → parse stringLit pos (chars ++ₗ suffix) ≡ nothing)
              (sym eq)
              (parseStringLit-fail-on-non-quote pos
                 (digitChar k) (tail ++ₗ suffix)
                 (digitChar-not-quote k k<10))
  parse-stringLit-fail-on-decRat pos (mkDecRat (+ suc n) a b cx) suffix
    with showDecRat-chars-head-digit (suc n) a b cx
  ... | k , tail , k<10 , eq =
        subst (λ chars → parse stringLit pos (chars ++ₗ suffix) ≡ nothing)
              (sym eq)
              (parseStringLit-fail-on-non-quote pos
                 (digitChar k) (tail ++ₗ suffix)
                 (digitChar-not-quote k k<10))
  parse-stringLit-fail-on-decRat pos (mkDecRat -[1+ n ] a b cx) suffix
    with showDecRat-chars-head-dash n a b cx
  ... | tail , eq =
        subst (λ chars → parse stringLit pos (chars ++ₗ suffix) ≡ nothing)
              (sym eq)
              (parseStringLit-fail-on-non-quote pos '-' (tail ++ₗ suffix) refl)

  -- `parse stringLit pos (showInt-chars z ++ suffix) ≡ nothing`.
  parse-stringLit-fail-on-int : ∀ pos z suffix
    → parse stringLit pos (showInt-chars z ++ₗ suffix) ≡ nothing
  parse-stringLit-fail-on-int pos (+ n) suffix with showNat-chars-head n
  ... | d , tail , d<10 , eq =
        subst (λ chars → parse stringLit pos (chars ++ₗ suffix) ≡ nothing)
              (sym eq)
              (parseStringLit-fail-on-non-quote pos
                 (digitChar d) (tail ++ₗ suffix)
                 (digitChar-not-quote d d<10))
  parse-stringLit-fail-on-int pos -[1+ n ] suffix =
    parseStringLit-fail-on-non-quote pos '-'
      (showNat-chars (suc n) ++ₗ suffix) refl

-- ============================================================================
-- DISJOINTNESS — parse decRatFrac fails on bare-int emit
-- ============================================================================
--
-- For the inner altSum's `inj₂` disjointness (intDecRat arm), we need
-- `parse decRatFrac pos (showInt-chars z ++ suffix) ≡ nothing`.
-- `parseDecRatFrac` parses optional '-', then digits, then *requires* '.'.
-- `showInt-chars z` is `(-)?` + digits with NO '.'.  After the digits the
-- parser sees the suffix's head, and the EmitsOK precondition for
-- `intDecRat` (`'.' ≢ headOr suffix '_'`) ensures that head isn't '.'.

private
  -- Helper: `parseDecRatFrac` reduction on `(- ?) digits-no-dot rest` where
  -- the post-digit suffix doesn't start with '.'.  The load-bearing
  -- disjointness for the 3-way altSum's inner `inj₂` (intDecRat branch).
  -- Requires `SuffixStops isDigit suffix` (the digit-bound stop) AND
  -- `'.' ≢ headOr suffix '_'` (no '.' at the suffix head — both come
  -- from the bareInt `EmitsOK intDecRat z suffix`).
  parse-decRatFrac-fail-on-bareInt :
    ∀ pos z suffix
    → SuffixStops isDigit suffix
    → '.' ≢ headOr suffix '_'
    → parse decRatFrac pos (showInt-chars z ++ₗ suffix) ≡ nothing
  parse-decRatFrac-fail-on-bareInt pos z suffix ss-digit not-dot =
    Aletheia.DBC.TextParser.DecRatParse.Properties.parseDecRatFrac-fails-bareInt
      z pos suffix ss-digit not-dot

-- ============================================================================
-- EMITS-OK BUILDERS — per-shape
-- ============================================================================

-- For shape RavwString s: outer altSum's inj₁ — only need EmitsOK stringLit.
-- The stringLit suffix-head precondition is `_≈ᵇ '"' suffix`-stopped.
build-EmitsOK-RavwString : ∀ (s : List Char) (suffix : List Char)
  → SuffixStops (λ c → c ≈ᵇ '"') suffix
  → EmitsOK attrValueWireFmt (RavwString s) suffix
build-EmitsOK-RavwString s suffix ss = ss

-- For shape RavwFrac d: outer altSum's inj₂ inj₁ — need:
--   1. inner EmitsOK decRatFrac d suffix = SuffixStops isDigit suffix
--   2. inner altSum disjointness: parse stringLit fails on decRatFrac emit
-- Plus: the inner altSum's inj₂ disjointness for the inj₂ inj₁ wrap is the
-- combined witness `EmitsOK decRatFrac d suffix × λ _ → refl-ish`.  Wait
-- actually inj₂ inj₁ = inj₁ inside the inner altSum; no extra disjointness
-- needed (left arm of inner altSum).
build-EmitsOK-RavwFrac : ∀ (d : DecRat) (suffix : List Char)
  → SuffixStops isDigit suffix
  → EmitsOK attrValueWireFmt (RavwFrac d) suffix
build-EmitsOK-RavwFrac d suffix ss-digit =
    -- Outer altSum (inj₂): inner EmitsOK + outer disjointness witness.
    inner-emit , (λ pos → parse-stringLit-fail-on-decRat pos d suffix)
  where
    -- Inner altSum (inj₁): just `EmitsOK decRatFrac d suffix`.
    inner-emit : EmitsOK (altSum decRatFrac intDecRat) (inj₁ d) suffix
    inner-emit = ss-digit

-- For shape RavwBareInt z: outer altSum's inj₂ inj₂ — need:
--   1. inner EmitsOK intDecRat z suffix = SuffixStops isDigit × ('.' ≢ head)
--   2. inner altSum disjointness: parse decRatFrac fails on intDecRat emit
--   3. outer altSum disjointness: parse stringLit fails on intDecRat emit
build-EmitsOK-RavwBareInt : ∀ (z : IntDecRat) (suffix : List Char)
  → SuffixStops isDigit suffix
  → '.' ≢ headOr suffix '_'
  → EmitsOK attrValueWireFmt (RavwBareInt z) suffix
build-EmitsOK-RavwBareInt z suffix ss-digit not-dot =
    -- Outer altSum (inj₂): (inner EmitsOK + inner disjointness) +
    --                      outer disjointness witness.
      ((ss-digit , not-dot)
      , (λ pos → parse-decRatFrac-fail-on-bareInt pos
                   (intDecRatToℤ z) suffix ss-digit not-dot))
    , (λ pos → parse-stringLit-fail-on-int pos (intDecRatToℤ z) suffix)

-- ============================================================================
-- UNIVERSAL ROUNDTRIP — single `roundtrip attrValueWireFmt` call
-- ============================================================================

parseRawAttrValueWire-format-roundtrip :
  ∀ (pos : Position) (rv : RawAttrValueWire) (suffix : List Char)
  → EmitsOK attrValueWireFmt rv suffix
  → parse attrValueWireFmt pos (emit attrValueWireFmt rv ++ₗ suffix)
    ≡ just (mkResult rv (advancePositions pos (emit attrValueWireFmt rv)) suffix)
parseRawAttrValueWire-format-roundtrip pos rv suffix wf =
  roundtrip attrValueWireFmt pos rv suffix wf
