{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.5.d 3c-B — DSL-side Format for the BA_DEF_DEF_ /
-- BA_ / BA_REL_ attribute lines + parseAttrLine 5-way `<|>` composer.
--
-- Mirrors `Format/AttrDef.agda` (3c-A) for the attribute-definition lines.
-- The crucial difference: 3c-B's value slot is shape-polymorphic (3 emit
-- shapes — RavwString / RavwFrac / RavwBareInt — see
-- `Format/AttrValue.agda`), routed through the universal `attrValueWireFmt`
-- 3-way altSum.  The line-level Format `attrDefaultFmt` etc. then plug
-- `attrValueWireFmt` into the value slot and wrap with the line's keyword
-- prefix + name + ws + ";\n" trailer.
--
-- Wire grammar slice:
--   attr-default ::= "BA_DEF_DEF_" ws string-lit ws attr-value ws? ";" newline
--   attr-assign  ::= "BA_" ws string-lit (ws attr-target)? ws attr-value
--                    ws? ";" newline
--   attr-rel     ::= "BA_REL_" ws string-lit ws rel-target ws attr-value
--                    ws? ";" newline
--   attr-line    ::= attr-def-rel <|> attr-default <|> attr-def <|>
--                    attr-rel <|> attr-assign      (5-way <|>)
--
-- The trailing `many parseNewline` consumption stays in the production
-- wrapper, NOT in this Format — same η-style wrap pattern as
-- `Format/EnvVar.agda` / `Format/AttrDef.agda`.

module Aletheia.DBC.TextParser.Format.AttrLine where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char; _≈ᵇ_)
open import Data.List using (List; []; _∷_) renaming (_++_ to _++ₗ_)
open import Data.List.Properties using () renaming (++-assoc to ++ₗ-assoc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; trans; subst)

open import Aletheia.Parser.Combinators
  using (Position; Parser; ParseResult; mkResult; advancePositions;
         _<|>_; _<$>_)
open import Data.Char.Base using (isDigit)
open import Aletheia.DBC.Identifier using (Identifier; isIdentCont)
open import Aletheia.DBC.DecRat.Refinement using (intDecRatToℤ)
open import Aletheia.DBC.TextParser.Lexer using (isHSpace)
open import Aletheia.DBC.TextParser.DecRatParse.Properties
  using (SuffixStops; ∷-stop; headOr; showNat-chars-head)
open import Aletheia.DBC.TextFormatter.Emitter using
  (digitChar; showNat-chars; showInt-chars; showDecRat-dec-chars;
   quoteStringLit-chars)
open import Aletheia.DBC.TextParser.Format
  using (Format; literal; ident; nat; stringLit; pair; iso; many;
         altSum; ws; wsOpt; wsCanonOne; withPrefix;
         emit; parse; EmitsOK; ParseFailsAt; roundtrip)
open import Aletheia.DBC.TextParser.Format.AttrValue
  using (RawAttrValueWire; RavwString; RavwFrac; RavwBareInt;
         attrValueWireFmt;
         build-EmitsOK-RavwString;
         build-EmitsOK-RavwFrac;
         build-EmitsOK-RavwBareInt;
         showInt-chars-head-stop;
         showDecRat-chars-head-stop;
         digit-not-isHSpace)

-- ============================================================================
-- LOCAL SUGAR — ws-aware combinators (same as Format/AttrDef.agda)
-- ============================================================================

-- Mandatory single space, parser one-or-more.  Public so emit reduction
-- of `attrDefaultFmt` etc. unfolds through `withWS` for the Properties
-- bridges in `Properties/Attributes/Default.agda`.
withWS : ∀ {A} → Format A → Format A
withWS f = iso proj₂ (λ a → tt , a) (λ _ → refl) (pair ws f)

-- Optional whitespace, parser zero-or-more.  Canonical emit `[]`.
withWSOpt : ∀ {A} → Format A → Format A
withWSOpt f = iso proj₂ (λ a → tt , a) (λ _ → refl) (pair wsOpt f)

-- Line terminator: accepts `"\r\n"` or `"\n"`, canonical emit `"\n"`.
newlineFmt : Format ⊤
newlineFmt = iso (λ _ → tt) (λ _ → inj₂ tt) (λ _ → refl)
                  (altSum (literal ('\r' ∷ '\n' ∷ []))
                          (literal ('\n' ∷ [])))

-- ============================================================================
-- BA_DEF_DEF_ LINE FORMAT
-- ============================================================================

-- Carrier: (name, value-wire, tt-trailing).
DefaultLineCarrier : Set
DefaultLineCarrier = List Char × RawAttrValueWire × ⊤

-- Wire shape:
--     BA_DEF_DEF_ "<name>" <value> ;\n
-- where `<value>` is dispatched to one of:
--     "<string>"      (RavwString shape)
--     <frac-form>     (RavwFrac shape — always contains '.')
--     <bare-int-form> (RavwBareInt shape — never contains '.')
-- via `attrValueWireFmt`'s 3-way altSum.
attrDefaultFmt : Format DefaultLineCarrier
attrDefaultFmt =
  withPrefix (toList "BA_DEF_DEF_") (
    withWS (
      pair stringLit (
        withWS (
          pair attrValueWireFmt (
            withWSOpt (
              withPrefix (';' ∷ []) newlineFmt))))))

-- ============================================================================
-- HEAD-NON-HSPACE DISPATCH ON VALUE-WIRE
-- ============================================================================

-- Head of `emit attrValueWireFmt rv ++ rest` is non-hspace.  Used for the
-- leading-ws slot precondition in `build-EmitsOK-attrDefaultFmt` (and
-- BA_/BA_REL_ siblings).  Per-shape: stringLit emits `'"' ∷ ...`,
-- decRatFrac/intDecRat emit a digit-or-'-' head — all non-hspace.
attrValue-emit-leading-non-hspace :
  ∀ (rv : RawAttrValueWire) (rest : List Char)
  → SuffixStops isHSpace (emit attrValueWireFmt rv ++ₗ rest)
attrValue-emit-leading-non-hspace (RavwString _) _ = ∷-stop refl
attrValue-emit-leading-non-hspace (RavwFrac d) rest =
  showDecRat-chars-head-stop d rest
attrValue-emit-leading-non-hspace (RavwBareInt z) rest =
  showInt-chars-head-stop (intDecRatToℤ z) rest

-- ++-assoc bridge for `(A ++ B) ++ outer ↔ A ++ (B ++ outer)` where the
-- leading ws slot's reduction lands on the LHS shape but our helpers
-- produce the RHS shape.  Mirror of `Format/AttrDef.agda`'s assoc-bridgeᴴ.
private
  assoc-bridgeᴴ : ∀ (xs as bs : List Char)
    → SuffixStops isHSpace (xs ++ₗ (as ++ₗ bs))
    → SuffixStops isHSpace ((xs ++ₗ as) ++ₗ bs)
  assoc-bridgeᴴ xs as bs ss =
    subst (SuffixStops isHSpace) (sym (++ₗ-assoc xs as bs)) ss

-- ============================================================================
-- EMITS-OK BUILDER FOR attrDefaultFmt
-- ============================================================================

-- 9-element EmitsOK tuple:
--   1. literal "BA_DEF_DEF_" — vacuous.
--   2. leading withWS after "BA_DEF_DEF_": SuffixStops isHSpace on
--      `(quoteStringLit-chars n ++ inner) ++ outer-suffix`.  Head is `'"'`.
--   3. stringLit body: SuffixStops `_≈ᵇ '"'` on `' ' ∷ ...`.  ∷-stop refl.
--   4. leading withWS after name: SuffixStops isHSpace on
--      `(emit attrValueWireFmt rv ++ ' ' ∷ ';' ∷ '\n' ∷ []) ++ outer-suffix`.
--      Per-shape head-stop dispatch.
--   5. attrValueWireFmt body: per-shape EmitsOK from build-EmitsOK-Ravw* with
--      suffix `' ' ∷ ';' ∷ '\n' ∷ outer-suffix`.  Wait — actually the
--      withWSOpt around `;` makes the suffix at the value slot just `;\n` +
--      outer (not ` ;\n`).  Let me re-check.
--
--      Actually looking at the structure: `pair attrValueWireFmt
--      (withWSOpt (withPrefix ";" newlineFmt))`.  The withWSOpt has empty
--      canonical emit — so the suffix at attrValueWireFmt's slot is
--      `(emit (withWSOpt ...) tt) ++ outer-suffix` = `(';' ∷ '\n' ∷ [])
--      ++ outer-suffix` = `';' ∷ '\n' ∷ outer-suffix`.  Confirmed.
--   6. leading withWSOpt after value: SuffixStops isHSpace on
--      `(emit (withPrefix ";" newlineFmt) tt) ++ outer-suffix` =
--      `(';' ∷ '\n' ∷ []) ++ outer-suffix`.  Head `';'` non-hspace.
--   7. literal ";" — vacuous.
--   8. newlineFmt iso — inj₂ inner.  literal "\n" vacuous.
--   9. newlineFmt altSum disjointness — parse "\r\n" on `'\n' ∷ os` fails
--      on first-char comparison.  λ _ → refl.

-- Per-shape EmitsOK at the value slot.  Each shape supplies a different
-- precondition: RavString needs `_≈ᵇ '"'` on the post-value suffix;
-- RavwFrac needs SuffixStops isDigit; RavwBareInt needs SuffixStops
-- isDigit AND `'.' ≢ headOr suffix '_'`.
--
-- For BA_DEF_DEF_, the suffix at the value slot is `;\n + outer-suffix`,
-- which has all 3 properties: head `';'` is not `'"'`, not digit, and
-- not `.`.

private
  -- Suffix at attrValueWireFmt slot.
  value-suffix : List Char → List Char
  value-suffix outer-suffix = ';' ∷ '\n' ∷ outer-suffix

  -- All three preconditions hold by ∷-stop refl on closed `';'` head.
  value-suffix-stops-quote :
    ∀ outer-suffix → SuffixStops (λ c → c ≈ᵇ '"') (value-suffix outer-suffix)
  value-suffix-stops-quote _ = ∷-stop refl

  value-suffix-stops-digit :
    ∀ outer-suffix → SuffixStops isDigit (value-suffix outer-suffix)
  value-suffix-stops-digit _ = ∷-stop refl

  value-suffix-not-dot :
    ∀ outer-suffix → '.' ≢ headOr (value-suffix outer-suffix) '_'
  value-suffix-not-dot _ = λ ()

build-EmitsOK-attrDefaultFmt :
  ∀ (n : List Char) (rv : RawAttrValueWire) (outer-suffix : List Char)
  → -- Per-shape value precondition supplied as an additional witness:
    EmitsOK attrValueWireFmt rv (value-suffix outer-suffix)
  → EmitsOK attrDefaultFmt (n , rv , tt) outer-suffix
build-EmitsOK-attrDefaultFmt n rv outer-suffix value-emit =
  -- L1: literal "BA_DEF_DEF_" — vacuous.
    tt
  -- L2: leading withWS after "BA_DEF_DEF_".  Head `'"'` from
  --     quoteStringLit-chars n.  ∷-stop refl.
  , ∷-stop refl
  -- L3: stringLit body — `_≈ᵇ '"'` on `' ' ∷ ...`.
  , ∷-stop refl
  -- L4: leading withWS after name.  Head non-hspace per shape.  The goal
  -- shape is `(emit attrValueWireFmt rv ++ (';' ∷ '\n' ∷ [])) ++ outer-suffix`;
  -- our head-stop helper produces `emit attrValueWireFmt rv ++ rest`, so
  -- bridge through ++-assoc.
  , assoc-bridgeᴴ (emit attrValueWireFmt rv) (';' ∷ '\n' ∷ []) outer-suffix
      (attrValue-emit-leading-non-hspace rv (';' ∷ '\n' ∷ outer-suffix))
  -- L5: attrValueWireFmt body — per-shape EmitsOK supplied by caller.
  , value-emit
  -- L6: leading withWSOpt after value.  Head `';'` non-hspace.
  , ∷-stop refl
  -- L7: literal ";" — vacuous.
  , tt
  -- L8: newlineFmt iso — literal "\n" vacuous.
  , tt
  -- L9: newlineFmt altSum disjointness.
  , λ _ → refl

-- ============================================================================
-- UNIVERSAL ROUNDTRIP — single `roundtrip attrDefaultFmt` call
-- ============================================================================

parseAttrDefault-format-roundtrip :
  ∀ (pos : Position) (n : List Char) (rv : RawAttrValueWire) (outer-suffix : List Char)
  → EmitsOK attrValueWireFmt rv (value-suffix outer-suffix)
  → parse attrDefaultFmt pos
      (emit attrDefaultFmt (n , rv , tt) ++ₗ outer-suffix)
    ≡ just (mkResult (n , rv , tt)
              (advancePositions pos
                (emit attrDefaultFmt (n , rv , tt)))
              outer-suffix)
parseAttrDefault-format-roundtrip pos n rv outer-suffix value-emit =
  roundtrip attrDefaultFmt pos (n , rv , tt) outer-suffix
            (build-EmitsOK-attrDefaultFmt n rv outer-suffix value-emit)

-- ============================================================================
-- BA_ LINE — std-target wire ADT + Format DSL
-- ============================================================================
--
-- 5-shape wire form for the BA_ target slot.  Pre-buildCANId: msg/sig
-- carry the raw `ℕ` from the wire.  The Format DSL maps each shape through
-- a different keyword arm; the empty arm (RatwNet) maps through `literal []`
-- for the no-target fall-through.  `liftStdTarget` (in `Attributes.agda`)
-- lifts wire→AST via `buildCANId` for the CAN-ID-bearing shapes (msg/sig),
-- with `Maybe`-fail for out-of-range raw IDs.
data RawAttrTargetWire : Set where
  RatwNode : Identifier → RawAttrTargetWire
  RatwMsg  : ℕ → RawAttrTargetWire
  RatwSig  : ℕ → Identifier → RawAttrTargetWire
  RatwEv   : Identifier → RawAttrTargetWire
  RatwNet  : RawAttrTargetWire

-- 2-shape wire form for the BA_REL_ target slot.  No empty arm — rel
-- target is mandatory in the BA_REL_ grammar.
data RawRelTargetWire : Set where
  RrtNodeMsg : Identifier → ℕ → RawRelTargetWire
  RrtNodeSig : Identifier → ℕ → Identifier → RawRelTargetWire

-- ============================================================================
-- KEYWORD ARMS — per-target Format leaves
-- ============================================================================
--
-- Each arm produces "<KW>_ " + body + " " — the trailing space mirrors the
-- production parsers' per-keyword `parseWS` after the body (consumed by
-- `parseStandardAttrTarget`'s convention).

-- Inner sugar: `pair ident ws` projected to just `Identifier` (drops the
-- trailing-ws `tt`).  Used by nodeArm/evArm/nodeMsgArm/etc. for the inner
-- "ident + trailing-ws" shape.
private
  identTrailingWS : Format Identifier
  identTrailingWS =
    iso proj₁ (λ n → n , tt) (λ _ → refl) (pair ident ws)

  -- Inner sugar: `pair nat ws` projected to just `ℕ`.
  natTrailingWS : Format ℕ
  natTrailingWS =
    iso proj₁ (λ r → r , tt) (λ _ → refl) (pair nat ws)

  -- "BU_" + ws + identifier + ws.
  nodeArm : Format Identifier
  nodeArm = withPrefix (toList "BU_") (withWS identTrailingWS)

  -- "BO_" + ws + nat + ws.
  msgArm : Format ℕ
  msgArm = withPrefix (toList "BO_") (withWS natTrailingWS)

  -- "SG_" + ws + nat + ws + ident + ws.  Carrier `ℕ × Identifier`.
  sigArm : Format (ℕ × Identifier)
  sigArm = withPrefix (toList "SG_") (
             withWS (
               pair nat (withWS identTrailingWS)))

  -- "EV_" + ws + identifier + ws.  Same shape as nodeArm.
  evArm : Format Identifier
  evArm = withPrefix (toList "EV_") (withWS identTrailingWS)

  -- Per-arm fails on inputs with abstract non-keyword head.  Each pinned
  -- by a single `with x ≈ᵇ <kw> | x≢kw` against the keyword's first char.
  -- Defined inside the `private` block so `parse <arm>` reduces locally
  -- through the `withPrefix → iso → pair → literal → parseCharsSeq → char
  -- → satisfy` chain — `satisfy` is the only consumer of the `_≈ᵇ_`
  -- result, so substituting `x ≈ᵇ <kw> = false` collapses the chain to
  -- `nothing` definitionally.  No EmitsOK reduction in the goal type.
  parseNodeArm-fails-on-non-B-head :
    ∀ (x : Char) (x≢B : (x ≈ᵇ 'B') ≡ false)
    → ∀ pos rest → parse nodeArm pos (x ∷ rest) ≡ nothing
  parseNodeArm-fails-on-non-B-head x x≢B pos rest with x ≈ᵇ 'B' | x≢B
  ... | false | refl = refl

  parseMsgArm-fails-on-non-B-head :
    ∀ (x : Char) (x≢B : (x ≈ᵇ 'B') ≡ false)
    → ∀ pos rest → parse msgArm pos (x ∷ rest) ≡ nothing
  parseMsgArm-fails-on-non-B-head x x≢B pos rest with x ≈ᵇ 'B' | x≢B
  ... | false | refl = refl

  parseSigArm-fails-on-non-S-head :
    ∀ (x : Char) (x≢S : (x ≈ᵇ 'S') ≡ false)
    → ∀ pos rest → parse sigArm pos (x ∷ rest) ≡ nothing
  parseSigArm-fails-on-non-S-head x x≢S pos rest with x ≈ᵇ 'S' | x≢S
  ... | false | refl = refl

  parseEvArm-fails-on-non-E-head :
    ∀ (x : Char) (x≢E : (x ≈ᵇ 'E') ≡ false)
    → ∀ pos rest → parse evArm pos (x ∷ rest) ≡ nothing
  parseEvArm-fails-on-non-E-head x x≢E pos rest with x ≈ᵇ 'E' | x≢E
  ... | false | refl = refl

  -- Tiny inline `<|>` and `<$>` step lemmas.  Mirror Primitives.agda's
  -- `alt-right-nothing` and Format.agda's `map-nothing` (the latter is
  -- in a private `where` block, not exported).  Each is a single-`with`
  -- proof — small in isolation.
  alt-right-nothing-local : ∀ {A : Set} (p q : Parser A) pos input
    → p pos input ≡ nothing → (p <|> q) pos input ≡ q pos input
  alt-right-nothing-local p _ pos input eq with p pos input | eq
  ... | nothing | refl = refl

  map-nothing-local : ∀ {A B : Set} (g : A → B) (p : Parser A) pos input
    → p pos input ≡ nothing → (g <$> p) pos input ≡ nothing
  map-nothing-local _ p pos input eq with p pos input | eq
  ... | nothing | refl = refl

  -- Compose 4 arm-fails into a single L1 fail via explicit `trans` chain.
  -- No `with` at the composition level — each step is a small lemma
  -- application (alt-right-nothing-local, map-nothing-local) over the
  -- already-proven arm fails.  This avoids the goal-rebuild cascade
  -- that `with`/`rewrite` over chained `<|>`/`<$>` triggers.
  parseStdTgtL1-fails-on-non-keyword-head :
    ∀ (x : Char)  -- explicit (avoid implicit-inference failure across `with`)
      (x≢B : (x ≈ᵇ 'B') ≡ false)
      (x≢S : (x ≈ᵇ 'S') ≡ false)
      (x≢E : (x ≈ᵇ 'E') ≡ false)
    → ∀ pos rest
    → parse (altSum (altSum (altSum nodeArm msgArm) sigArm) evArm) pos (x ∷ rest) ≡ nothing
  parseStdTgtL1-fails-on-non-keyword-head x x≢B x≢S x≢E pos rest =
    let
      -- parse nodeArm fails via x ≢ 'B'.
      node-f : parse nodeArm pos (x ∷ rest) ≡ nothing
      node-f = parseNodeArm-fails-on-non-B-head x x≢B pos rest
      -- parse msgArm fails via x ≢ 'B'.
      msg-f : parse msgArm pos (x ∷ rest) ≡ nothing
      msg-f = parseMsgArm-fails-on-non-B-head x x≢B pos rest
      -- parse sigArm fails via x ≢ 'S'.
      sig-f : parse sigArm pos (x ∷ rest) ≡ nothing
      sig-f = parseSigArm-fails-on-non-S-head x x≢S pos rest
      -- parse evArm fails via x ≢ 'E'.
      ev-f : parse evArm pos (x ∷ rest) ≡ nothing
      ev-f = parseEvArm-fails-on-non-E-head x x≢E pos rest

      -- L3 = altSum nodeArm msgArm.  parse L3 pos input
      -- = (inj₁ <$> parse nodeArm) <|> (inj₂ <$> parse msgArm)
      -- → (nothing) <|> (inj₂ <$> parse msgArm) → (inj₂ <$> parse msgArm)
      -- → (inj₂ <$> nothing) → nothing.
      L3-f : parse (altSum nodeArm msgArm) pos (x ∷ rest) ≡ nothing
      L3-f = trans
               (alt-right-nothing-local (inj₁ <$> parse nodeArm)
                  (inj₂ <$> parse msgArm) pos (x ∷ rest)
                  (map-nothing-local inj₁ (parse nodeArm) pos (x ∷ rest) node-f))
               (map-nothing-local inj₂ (parse msgArm) pos (x ∷ rest) msg-f)

      -- L2 = altSum L3 sigArm.  Same structure.
      L2-f : parse (altSum (altSum nodeArm msgArm) sigArm) pos (x ∷ rest) ≡ nothing
      L2-f = trans
               (alt-right-nothing-local (inj₁ <$> parse (altSum nodeArm msgArm))
                  (inj₂ <$> parse sigArm) pos (x ∷ rest)
                  (map-nothing-local inj₁ (parse (altSum nodeArm msgArm))
                     pos (x ∷ rest) L3-f))
               (map-nothing-local inj₂ (parse sigArm) pos (x ∷ rest) sig-f)
    in
    -- L1 = altSum L2 evArm.
    trans
      (alt-right-nothing-local
         (inj₁ <$> parse (altSum (altSum nodeArm msgArm) sigArm))
         (inj₂ <$> parse evArm) pos (x ∷ rest)
         (map-nothing-local inj₁ (parse (altSum (altSum nodeArm msgArm) sigArm))
            pos (x ∷ rest) L2-f))
      (map-nothing-local inj₂ (parse evArm) pos (x ∷ rest) ev-f)

-- ============================================================================
-- STD TARGET FORMAT — 5-way altSum + iso (Net via empty arm)
-- ============================================================================

private
  -- 5-way altSum carrier: ((((Node ⊎ Msg) ⊎ Sig) ⊎ Ev) ⊎ Net)
  StdTargetWireCarrier : Set
  StdTargetWireCarrier =
    ((((Identifier ⊎ ℕ) ⊎ (ℕ × Identifier)) ⊎ Identifier) ⊎ ⊤)

  stdTargetWireCarrierFmt : Format StdTargetWireCarrier
  stdTargetWireCarrierFmt =
    altSum (
      altSum (
        altSum (
          altSum nodeArm msgArm) sigArm) evArm) (literal [])

  fwdStdTgt : StdTargetWireCarrier → RawAttrTargetWire
  fwdStdTgt (inj₁ (inj₁ (inj₁ (inj₁ n))))     = RatwNode n
  fwdStdTgt (inj₁ (inj₁ (inj₁ (inj₂ raw))))    = RatwMsg raw
  fwdStdTgt (inj₁ (inj₁ (inj₂ (raw , sig))))   = RatwSig raw sig
  fwdStdTgt (inj₁ (inj₂ ev))                    = RatwEv ev
  fwdStdTgt (inj₂ tt)                           = RatwNet

  bwdStdTgt : RawAttrTargetWire → StdTargetWireCarrier
  bwdStdTgt (RatwNode n)    = inj₁ (inj₁ (inj₁ (inj₁ n)))
  bwdStdTgt (RatwMsg raw)   = inj₁ (inj₁ (inj₁ (inj₂ raw)))
  bwdStdTgt (RatwSig r s)   = inj₁ (inj₁ (inj₂ (r , s)))
  bwdStdTgt (RatwEv ev)     = inj₁ (inj₂ ev)
  bwdStdTgt RatwNet          = inj₂ tt

  fwdStdTgt-bwdStdTgt : ∀ wt → fwdStdTgt (bwdStdTgt wt) ≡ wt
  fwdStdTgt-bwdStdTgt (RatwNode _)   = refl
  fwdStdTgt-bwdStdTgt (RatwMsg _)    = refl
  fwdStdTgt-bwdStdTgt (RatwSig _ _)  = refl
  fwdStdTgt-bwdStdTgt (RatwEv _)     = refl
  fwdStdTgt-bwdStdTgt RatwNet         = refl

stdTargetWireFmt : Format RawAttrTargetWire
stdTargetWireFmt =
  iso fwdStdTgt bwdStdTgt fwdStdTgt-bwdStdTgt stdTargetWireCarrierFmt

-- ============================================================================
-- REL TARGET FORMAT — 2-way altSum + iso
-- ============================================================================

private
  -- "BU_BO_REL_" + ws + ident + ws + nat + ws.  Carrier `Identifier × ℕ`.
  nodeMsgArm : Format (Identifier × ℕ)
  nodeMsgArm = withPrefix (toList "BU_BO_REL_") (
                 withWS (
                   pair ident (withWS natTrailingWS)))

  -- "BU_SG_REL_" + ws + ident + ws + "SG_" + ws + nat + ws + ident + ws.
  -- Carrier `Identifier × ℕ × Identifier`.
  nodeSigArm : Format (Identifier × ℕ × Identifier)
  nodeSigArm = withPrefix (toList "BU_SG_REL_") (
                 withWS (
                   pair ident (
                     withWS (
                       withPrefix (toList "SG_") (
                         withWS (
                           pair nat (withWS identTrailingWS)))))))

  RelTargetWireCarrier : Set
  RelTargetWireCarrier = (Identifier × ℕ) ⊎ (Identifier × ℕ × Identifier)

  relTargetWireCarrierFmt : Format RelTargetWireCarrier
  relTargetWireCarrierFmt = altSum nodeMsgArm nodeSigArm

  fwdRelTgt : RelTargetWireCarrier → RawRelTargetWire
  fwdRelTgt (inj₁ (n , r))        = RrtNodeMsg n r
  fwdRelTgt (inj₂ (n , r , s))    = RrtNodeSig n r s

  bwdRelTgt : RawRelTargetWire → RelTargetWireCarrier
  bwdRelTgt (RrtNodeMsg n r)    = inj₁ (n , r)
  bwdRelTgt (RrtNodeSig n r s)  = inj₂ (n , r , s)

  fwdRelTgt-bwdRelTgt : ∀ rt → fwdRelTgt (bwdRelTgt rt) ≡ rt
  fwdRelTgt-bwdRelTgt (RrtNodeMsg _ _)   = refl
  fwdRelTgt-bwdRelTgt (RrtNodeSig _ _ _) = refl

relTargetWireFmt : Format RawRelTargetWire
relTargetWireFmt =
  iso fwdRelTgt bwdRelTgt fwdRelTgt-bwdRelTgt relTargetWireCarrierFmt

-- ============================================================================
-- LINE FORMATS — attrAssignFmt (BA_) / attrRelFmt (BA_REL_)
-- ============================================================================

-- Carriers: line-shape tuples carrying name + wire-target + wire-value +
-- ⊤-trailing.  The trailing `⊤` is the result of the `withWSOpt; ";";
-- newlineFmt` chain.
AttrAssignCarrier : Set
AttrAssignCarrier = List Char × RawAttrTargetWire × RawAttrValueWire × ⊤

AttrRelCarrier : Set
AttrRelCarrier = List Char × RawRelTargetWire × RawAttrValueWire × ⊤

-- BA_ line.  Wire shape:
--     BA_ "<name>" <target-prefix-or-empty><value> ;\n
-- where `<target-prefix-or-empty>` is `[]` for ATgtNetwork (the empty arm
-- of stdTargetWireFmt) or `<KW>_ <body> ` for the four standard scopes.
attrAssignFmt : Format AttrAssignCarrier
attrAssignFmt =
  withPrefix (toList "BA_") (
    withWS (
      pair stringLit (
        pair (withWS stdTargetWireFmt) (
          pair attrValueWireFmt (
            withWSOpt (
              withPrefix (';' ∷ []) newlineFmt))))))

-- BA_REL_ line.  Wire shape:
--     BA_REL_ "<name>" <rel-target> <value> ;\n
-- with mandatory rel-target (no empty arm in relTargetWireFmt).
attrRelFmt : Format AttrRelCarrier
attrRelFmt =
  withPrefix (toList "BA_REL_") (
    withWS (
      pair stringLit (
        pair (withWS relTargetWireFmt) (
          pair attrValueWireFmt (
            withWSOpt (
              withPrefix (';' ∷ []) newlineFmt))))))

-- ============================================================================
-- LINE-LEVEL EMITS-OK BUILDER (C(ii) — single generic builder)
-- ============================================================================
--
-- The line Format's EmitsOK has 10 slots after structural reduction.  Eight
-- are constants (closed-Char head dispatches on `'B'`/`'"'`/`' '`/`';'`/
-- `'\n'`).  Two slots vary per call: L4 (head non-hspace at the post-name
-- ws slot — depends on target shape's emit head) and L5 (per-target altSum
-- EmitsOK — depends on which target arm).  Plus L6 (per-value altSum
-- EmitsOK) is always supplied by the caller.
--
-- Caller convention: L4/L5/L6 inputs use the *canonical* right-associated
-- suffix shape (`emit attrValueWireFmt wireVal ++ ';' ∷ '\n' ∷ outer-suffix`).
-- The builder bridges via `++ₗ-assoc` to Agda's left-associated natural
-- shape (`emit (pair attrValueWireFmt (withWSOpt (withPrefix ";" newlineFmt)))
-- (wireVal , tt) ++ outer-suffix`) — this is needed because the inner
-- `emit (withWSOpt ...) tt` reduces to `';' ∷ '\n' ∷ []` definitionally,
-- but the outer associativity of `_++_` is propositional, not definitional.

private
  -- Bridge: convert canonical right-assoc `value-emit ++ ';' ∷ '\n' ∷ os`
  -- to Agda's left-assoc `(value-emit ++ ';' ∷ '\n' ∷ []) ++ os` shape.
  -- Pure subst on `++ₗ-assoc`.
  rebracket-tail : ∀ (xs : List Char) (outer-suffix : List Char)
    → xs ++ₗ ';' ∷ '\n' ∷ outer-suffix
      ≡ (xs ++ₗ ';' ∷ '\n' ∷ []) ++ₗ outer-suffix
  rebracket-tail xs outer-suffix = sym (++ₗ-assoc xs (';' ∷ '\n' ∷ []) outer-suffix)

  -- Bridge: convert canonical right-assoc `target-emit ++ value-emit ++ ;\n+os`
  -- to Agda's left-assoc `target-emit ++ (value-emit ++ ;\n+[]) ++ os` shape.
  -- Two-step: first inner rebracket-tail, then outer ++-cong.
  rebracket-tail3 : ∀ (xs ys : List Char) (outer-suffix : List Char)
    → xs ++ₗ ys ++ₗ ';' ∷ '\n' ∷ outer-suffix
      ≡ xs ++ₗ (ys ++ₗ ';' ∷ '\n' ∷ []) ++ₗ outer-suffix
  rebracket-tail3 xs ys outer-suffix =
    cong (xs ++ₗ_) (rebracket-tail ys outer-suffix)

-- Universal roundtrip for `attrAssignFmt`.  A thin wrapper around
-- `roundtrip attrAssignFmt` that takes the 3 per-shape EmitsOK pieces
-- (L4 head witness, L5 target body, L6 value body) and discharges the
-- 7 constants inline.  L4/L5/L6 use the canonical right-assoc shape;
-- builder bridges via `++ₗ-assoc` substs.
parseAttrAssign-format-roundtrip :
  ∀ (pos : Position) (n : List Char)
    (wireTgt : RawAttrTargetWire) (wireVal : RawAttrValueWire)
    (outer-suffix : List Char)
  → SuffixStops isHSpace
      (emit stdTargetWireFmt wireTgt ++ₗ
       emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)
  → EmitsOK stdTargetWireFmt wireTgt
      (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)
  → EmitsOK attrValueWireFmt wireVal (';' ∷ '\n' ∷ outer-suffix)
  → parse attrAssignFmt pos
      (emit attrAssignFmt (n , wireTgt , wireVal , tt) ++ₗ outer-suffix)
    ≡ just (mkResult (n , wireTgt , wireVal , tt)
              (advancePositions pos
                (emit attrAssignFmt (n , wireTgt , wireVal , tt)))
              outer-suffix)
parseAttrAssign-format-roundtrip pos n wireTgt wireVal outer-suffix l4 l5 l6 =
  roundtrip attrAssignFmt pos (n , wireTgt , wireVal , tt) outer-suffix
    -- L1: literal "BA_"
    ( tt
    -- L2: leading withWS after BA_, head '"' from quoteStringLit-chars n
    , ∷-stop refl
    -- L3: stringLit body, head ' ' (leading ws of post-name withWS)
    , ∷-stop refl
    -- (L4, L5): paired from `withWS stdTargetWireFmt` expansion.  Bridge
    -- via subst on rebracket-tail3 (L4) / rebracket-tail (L5).
    , ( subst (SuffixStops isHSpace)
              (rebracket-tail3 (emit stdTargetWireFmt wireTgt)
                               (emit attrValueWireFmt wireVal)
                               outer-suffix)
              l4
      , subst (EmitsOK stdTargetWireFmt wireTgt)
              (rebracket-tail (emit attrValueWireFmt wireVal) outer-suffix)
              l5
      )
    -- L6: attrValueWireFmt body — caller-supplied (canonical shape OK).
    , l6
    -- L7: leading withWSOpt after value, head ';'
    , ∷-stop refl
    -- L8: literal ";"
    , tt
    -- L9: newlineFmt iso → inj₂ tt → literal "\n"
    , tt
    -- L10: newlineFmt altSum disjointness — '\r' ≢ '\n' on closed head
    , λ _ → refl
    )

-- Universal roundtrip for `attrRelFmt`.  Same structure as attrAssignFmt
-- but with `relTargetWireFmt` at the L5 slot.  L1's literal is "BA_REL_"
-- (longer prefix) — that's the only structural difference from
-- `attrAssignFmt`.  L4/L5/L6 supplied by caller in canonical shape.
parseAttrRel-format-roundtrip :
  ∀ (pos : Position) (n : List Char)
    (wireTgt : RawRelTargetWire) (wireVal : RawAttrValueWire)
    (outer-suffix : List Char)
  → SuffixStops isHSpace
      (emit relTargetWireFmt wireTgt ++ₗ
       emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)
  → EmitsOK relTargetWireFmt wireTgt
      (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)
  → EmitsOK attrValueWireFmt wireVal (';' ∷ '\n' ∷ outer-suffix)
  → parse attrRelFmt pos
      (emit attrRelFmt (n , wireTgt , wireVal , tt) ++ₗ outer-suffix)
    ≡ just (mkResult (n , wireTgt , wireVal , tt)
              (advancePositions pos
                (emit attrRelFmt (n , wireTgt , wireVal , tt)))
              outer-suffix)
parseAttrRel-format-roundtrip pos n wireTgt wireVal outer-suffix l4 l5 l6 =
  roundtrip attrRelFmt pos (n , wireTgt , wireVal , tt) outer-suffix
    ( tt
    , ∷-stop refl
    , ∷-stop refl
    , ( subst (SuffixStops isHSpace)
              (rebracket-tail3 (emit relTargetWireFmt wireTgt)
                               (emit attrValueWireFmt wireVal)
                               outer-suffix)
              l4
      , subst (EmitsOK relTargetWireFmt wireTgt)
              (rebracket-tail (emit attrValueWireFmt wireVal) outer-suffix)
              l5
      )
    , l6
    , ∷-stop refl
    , tt
    , tt
    , λ _ → refl
    )

-- ============================================================================
-- PUBLIC EMIT-EQUATIONS — exported for Properties-side bridges
-- ============================================================================
--
-- Format/AttrLine.agda's keyword arms / scope iso wrappers / line Formats
-- are defined with `private` helpers that block external reduction (e.g.
-- `stdTargetWireCarrierFmt` is private, so Network.agda can't reduce
-- `emit stdTargetWireFmt RatwNet` directly).  The lemmas below expose
-- the closed-form emit equalities, all closed by `refl` within this
-- module's scope.

-- Per-target-shape emit equalities for stdTargetWireFmt.
emit-stdTargetWireFmt-RatwNet : emit stdTargetWireFmt RatwNet ≡ []
emit-stdTargetWireFmt-RatwNet = refl

emit-stdTargetWireFmt-RatwNode : ∀ (n : Identifier) →
  emit stdTargetWireFmt (RatwNode n)
  ≡ toList "BU_" ++ₗ ' ' ∷ Identifier.name n ++ₗ ' ' ∷ []
emit-stdTargetWireFmt-RatwNode _ = refl

emit-stdTargetWireFmt-RatwMsg : ∀ (raw : ℕ) →
  emit stdTargetWireFmt (RatwMsg raw)
  ≡ toList "BO_" ++ₗ ' ' ∷ emit nat raw ++ₗ ' ' ∷ []
emit-stdTargetWireFmt-RatwMsg _ = refl

emit-stdTargetWireFmt-RatwSig : ∀ (raw : ℕ) (sig : Identifier) →
  emit stdTargetWireFmt (RatwSig raw sig)
  ≡ toList "SG_" ++ₗ ' ' ∷ (emit nat raw ++ₗ
      ' ' ∷ Identifier.name sig ++ₗ ' ' ∷ [])
emit-stdTargetWireFmt-RatwSig _ _ = refl

emit-stdTargetWireFmt-RatwEv : ∀ (ev : Identifier) →
  emit stdTargetWireFmt (RatwEv ev)
  ≡ toList "EV_" ++ₗ ' ' ∷ Identifier.name ev ++ₗ ' ' ∷ []
emit-stdTargetWireFmt-RatwEv _ = refl

-- Per-target-shape emit equalities for relTargetWireFmt.
emit-relTargetWireFmt-RrtNodeMsg : ∀ (n : Identifier) (raw : ℕ) →
  emit relTargetWireFmt (RrtNodeMsg n raw)
  ≡ toList "BU_BO_REL_" ++ₗ ' ' ∷ (Identifier.name n ++ₗ
      ' ' ∷ emit nat raw ++ₗ ' ' ∷ [])
emit-relTargetWireFmt-RrtNodeMsg _ _ = refl

emit-relTargetWireFmt-RrtNodeSig : ∀ (n : Identifier) (raw : ℕ) (sig : Identifier) →
  emit relTargetWireFmt (RrtNodeSig n raw sig)
  ≡ toList "BU_SG_REL_" ++ₗ ' ' ∷ (Identifier.name n ++ₗ
      ' ' ∷ (toList "SG_" ++ₗ ' ' ∷ (emit nat raw ++ₗ
        ' ' ∷ Identifier.name sig ++ₗ ' ' ∷ [])))
emit-relTargetWireFmt-RrtNodeSig _ _ _ = refl

-- Network arm full-line emit: empty target slot collapses inline.  The
-- only Format-DSL line shape that closes by `refl` without ++ₗ-assoc
-- bridges (since RatwNet emits `[]` and the slot disappears).
emit-attrAssignFmt-RatwNet :
  ∀ (n : List Char) (wireVal : RawAttrValueWire) →
  emit attrAssignFmt (n , RatwNet , wireVal , tt)
  ≡ toList "BA_ " ++ₗ quoteStringLit-chars n ++ₗ
      ' ' ∷ (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ [])
emit-attrAssignFmt-RatwNet _ _ = refl

-- Composite bridge for keyword-target lines: emit ++ outer-suffix in the
-- inline-input shape.  Combines `shift-trail-space`-style tail merging
-- with the trailing `;\n` ++-assoc bridge.  Used by per-target Properties
-- files for the dispatcher's input-bridge.
private
  -- (xs ++ ' ' ∷ []) ++ ys ≡ xs ++ ' ' ∷ ys.  Pure ++-assoc.
  shift-trail-space-AttrLine : ∀ (xs ys : List Char)
    → (xs ++ₗ ' ' ∷ []) ++ₗ ys ≡ xs ++ₗ ' ' ∷ ys
  shift-trail-space-AttrLine xs ys = ++ₗ-assoc xs (' ' ∷ []) ys

  -- Generic bridge for the line-shape `(qsl(name) ++ ' ∷ kw-body ++ (value-chars
  -- ++ ;\n+[])) ++ outer-suffix ↔ qsl(name) ++ ' ∷ kw-body ++ value-chars ++
  -- ;\n+ outer-suffix`.  Three nested ++-assoc steps:
  --   1. `qsl ++ (' ∷ STUFF)` ↔ outer pull through qsl.
  --   2. `kw-body ++ (value ++ ;\n+[])` ↔ outer pull through kw-body.
  --   3. `value ++ (;\n+[])` ↔ outer pull through value.
  -- Treats `kw-body` opaquely; identical proof for Node/Msg/Sig/Ev kw-bodies.
  -- Also reused by attrRelFmt (BA_REL_) which has the same line-tail shape.
  bridge-emit-tail :
    ∀ (name : List Char) (kw-body : List Char) (value-chars : List Char)
      (outer-suffix : List Char)
    → (quoteStringLit-chars name ++ₗ
         ' ' ∷ kw-body ++ₗ (value-chars ++ₗ ';' ∷ '\n' ∷ []))
        ++ₗ outer-suffix
      ≡ quoteStringLit-chars name ++ₗ
          ' ' ∷ kw-body ++ₗ value-chars ++ₗ ';' ∷ '\n' ∷ outer-suffix
  bridge-emit-tail name kw-body value-chars outer-suffix =
    trans
      (++ₗ-assoc (quoteStringLit-chars name)
                 (' ' ∷ kw-body ++ₗ (value-chars ++ₗ ';' ∷ '\n' ∷ []))
                 outer-suffix)
      (cong (λ z → quoteStringLit-chars name ++ₗ ' ' ∷ z)
            (trans
              (++ₗ-assoc kw-body (value-chars ++ₗ ';' ∷ '\n' ∷ []) outer-suffix)
              (cong (kw-body ++ₗ_)
                    (++ₗ-assoc value-chars (';' ∷ '\n' ∷ []) outer-suffix))))

-- ============================================================================
-- L5 DISJOINTNESS HELPERS — `EmitsOK stdTargetWireFmt RatwNet input`
-- ============================================================================
--
-- The L5 obligation of `parseAttrAssign-format-roundtrip` for `wireTgt =
-- RatwNet` reduces (via `iso` then `altSum (inj₂ tt)`) to:
--   ⊤ × (∀ pos → parse <left-keyword-chain> pos input ≡ nothing)
-- where `<left-keyword-chain>` is the private `(((nodeArm | msgArm) | sigArm)
-- | evArm)` 4-way altSum.  Each arm starts with `withPrefix "BU_"/"BO_"/
-- "SG_"/"EV_"`, parsing its first char.  For inputs whose first char is
-- not in `{'B','S','E'}`, all four arms fail by first-char `_≈ᵇ_` mismatch
-- and the chain returns `nothing` — `λ _ → refl` closes the disjointness
-- locally (here, where left-chain is in private scope).
--
-- For the 3 ATgtNetwork value-emit shapes, the leading char is one of:
--   * `'"'`        (RavwString)
--   * digit-or-`'-'` (RavwFrac, RavwBareInt — head-classify dispatched
--                    by the caller in `Properties/.../Network.agda`).
--
-- Each helper below takes the input plus an equality `input ≡ <head> ∷ tail`
-- and pattern-matches on `refl` to expose the closed head locally, sidestep-
-- ping `subst` over the (huge) `EmitsOK stdTargetWireFmt RatwNet …` predicate
-- — pattern-matching `refl` does NOT trigger predicate reduction, while
-- `subst` does, blowing -M16G via the 4-deep nested altSum.
--
-- The per-`k` digit dispatch is closed by 10 explicit cases + an absurd
-- suc-chain (matches `Common.agda`'s `digitChar-not-quote` shape).  For
-- closed `'"'` and `'-'` heads, `λ _ → refl` is used directly.

emit-stdTargetWireFmt-RatwNet-on-quote-head :
  ∀ (input : List Char) (rest : List Char)
  → input ≡ '"' ∷ rest
  → EmitsOK stdTargetWireFmt RatwNet input
emit-stdTargetWireFmt-RatwNet-on-quote-head _ _ refl = (tt , λ _ → refl)

emit-stdTargetWireFmt-RatwNet-on-dash-head :
  ∀ (input : List Char) (rest : List Char)
  → input ≡ '-' ∷ rest
  → EmitsOK stdTargetWireFmt RatwNet input
emit-stdTargetWireFmt-RatwNet-on-dash-head _ _ refl = (tt , λ _ → refl)

emit-stdTargetWireFmt-RatwNet-on-digit-head :
  ∀ (input : List Char) (k : ℕ) → k Data.Nat.< 10
  → ∀ (rest : List Char)
  → input ≡ digitChar k ∷ rest
  → EmitsOK stdTargetWireFmt RatwNet input
emit-stdTargetWireFmt-RatwNet-on-digit-head _ 0 _ _ refl = (tt , λ _ → refl)
emit-stdTargetWireFmt-RatwNet-on-digit-head _ 1 _ _ refl = (tt , λ _ → refl)
emit-stdTargetWireFmt-RatwNet-on-digit-head _ 2 _ _ refl = (tt , λ _ → refl)
emit-stdTargetWireFmt-RatwNet-on-digit-head _ 3 _ _ refl = (tt , λ _ → refl)
emit-stdTargetWireFmt-RatwNet-on-digit-head _ 4 _ _ refl = (tt , λ _ → refl)
emit-stdTargetWireFmt-RatwNet-on-digit-head _ 5 _ _ refl = (tt , λ _ → refl)
emit-stdTargetWireFmt-RatwNet-on-digit-head _ 6 _ _ refl = (tt , λ _ → refl)
emit-stdTargetWireFmt-RatwNet-on-digit-head _ 7 _ _ refl = (tt , λ _ → refl)
emit-stdTargetWireFmt-RatwNet-on-digit-head _ 8 _ _ refl = (tt , λ _ → refl)
emit-stdTargetWireFmt-RatwNet-on-digit-head _ 9 _ _ refl = (tt , λ _ → refl)
emit-stdTargetWireFmt-RatwNet-on-digit-head _
  (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _))))))))))
  (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s
    (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s (Data.Nat.s≤s ()))))))))))

-- Abstract-head EmitsOK builder.  Takes head-class witness (head + 3 ≢
-- inequalities against keyword first chars) and produces the L5 disjoint-
-- ness witness without the 11-case digit dispatch the on-digit-head trio
-- needs.  The body pair-constructs `(tt , λ pos → parseStdTgtL1-fails ...)`
-- — verified against `EmitsOK stdTargetWireFmt RatwNet (x ∷ rest)`'s
-- ⊤ × Π reduction by a single normalization (no `with` blowup since the
-- disjointness Π is supplied directly as an argument, never reconstructed
-- in scope).  Used by `parseAttrAssign-format-roundtrip-RatwNet`.

emit-stdTargetWireFmt-RatwNet-on-non-keyword-head :
  ∀ (input : List Char) (x : Char) (rest : List Char)
  → input ≡ x ∷ rest
  → (x ≈ᵇ 'B') ≡ false
  → (x ≈ᵇ 'S') ≡ false
  → (x ≈ᵇ 'E') ≡ false
  → EmitsOK stdTargetWireFmt RatwNet input
emit-stdTargetWireFmt-RatwNet-on-non-keyword-head _ x rest refl x≢B x≢S x≢E =
  (tt , λ pos → parseStdTgtL1-fails-on-non-keyword-head x x≢B x≢S x≢E pos rest)

-- Specialized RatwNet roundtrip — takes a head-class witness instead of
-- the wide `EmitsOK stdTargetWireFmt RatwNet …` obligation that the
-- universal lemma wants for L5.  See `feedback_emitsok_inj2_deep_pattern.md`
-- for why the universal-lemma path OOMs for RatwNet.  Internally builds
-- the L5 via `emit-stdTargetWireFmt-RatwNet-on-non-keyword-head` and
-- delegates to the universal lemma.  Network.agda's per-shape dispatchers
-- consume this with head-class witnesses derived from `showXxx-chars-
-- head-classify`.
parseAttrAssign-format-roundtrip-RatwNet :
  ∀ (pos : Position) (n : List Char)
    (wireVal : RawAttrValueWire) (outer-suffix : List Char)
    (x : Char) (tail : List Char)
  → SuffixStops isHSpace
      (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)
  → EmitsOK attrValueWireFmt wireVal (';' ∷ '\n' ∷ outer-suffix)
  → emit attrValueWireFmt wireVal ≡ x ∷ tail
  → (x ≈ᵇ 'B') ≡ false
  → (x ≈ᵇ 'S') ≡ false
  → (x ≈ᵇ 'E') ≡ false
  → parse attrAssignFmt pos
      (emit attrAssignFmt (n , RatwNet , wireVal , tt) ++ₗ outer-suffix)
    ≡ just (mkResult (n , RatwNet , wireVal , tt)
              (advancePositions pos
                (emit attrAssignFmt (n , RatwNet , wireVal , tt)))
              outer-suffix)
parseAttrAssign-format-roundtrip-RatwNet pos n wireVal outer-suffix x tail
                                          l4 l6 val-eq x≢B x≢S x≢E =
  parseAttrAssign-format-roundtrip pos n RatwNet wireVal outer-suffix l4
    (emit-stdTargetWireFmt-RatwNet-on-non-keyword-head
       (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix)
       x
       (tail ++ₗ ';' ∷ '\n' ∷ outer-suffix)
       (cong (_++ₗ ';' ∷ '\n' ∷ outer-suffix) val-eq)
       x≢B x≢S x≢E)
    l6

-- ============================================================================
-- KEYWORD-TARGET EMIT EQUATIONS — public, full-line attrAssignFmt shapes
-- ============================================================================
--
-- Mirror of `emit-attrAssignFmt-RatwNet` for the 4 keyword targets.  Each
-- exposes the closed-form emit equality so the per-target Properties files
-- can bridge between the inline-input shape (`"BA_ " ++ qsl(name) ++
-- " <KW>_ " ++ <body> ++ ' ' ∷ value-chars ++ ";\n" ++ outer`) and the
-- universal `parseAttrAssign-format-roundtrip`'s `emit attrAssignFmt …`
-- input.  All close by `refl` here (private internals reduce in scope).

emit-attrAssignFmt-RatwNode :
  ∀ (n : List Char) (idn : Identifier) (wireVal : RawAttrValueWire) →
  emit attrAssignFmt (n , RatwNode idn , wireVal , tt)
  ≡ toList "BA_ " ++ₗ quoteStringLit-chars n ++ₗ
      ' ' ∷ (toList "BU_" ++ₗ ' ' ∷ Identifier.name idn ++ₗ ' ' ∷ []) ++ₗ
        (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ [])
emit-attrAssignFmt-RatwNode _ _ _ = refl

-- Outer-suffix variant: bakes outer-suffix into the canonical spec shape
-- (`"BA_ " ++ qsl(n) ++ " BU_ " ++ name idn ++ ' ∷ value-emit ++ ;\n+
-- outer-suffix`) — the form per-target dispatcher inputs use.  Composed
-- via `bridge-emit-tail` (3 nested ++-assoc steps over qsl/kw-body/value)
-- + one final ++-assoc over `name idn ++ ' ∷ []` to fold the trailing
-- ws-slot of `identTrailingWS` into the leading ' ∷ value-chars.
emit-attrAssignFmt-RatwNode-with-outer :
  ∀ (n : List Char) (idn : Identifier) (wireVal : RawAttrValueWire)
    (outer-suffix : List Char) →
  emit attrAssignFmt (n , RatwNode idn , wireVal , tt) ++ₗ outer-suffix
  ≡ toList "BA_ " ++ₗ quoteStringLit-chars n ++ₗ
      toList " BU_ " ++ₗ Identifier.name idn ++ₗ
      ' ' ∷ emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix
emit-attrAssignFmt-RatwNode-with-outer n idn wireVal outer-suffix =
  trans
    (cong (_++ₗ outer-suffix) (emit-attrAssignFmt-RatwNode n idn wireVal))
    (trans
      (cong (λ z → toList "BA_ " ++ₗ z)
            (bridge-emit-tail n
              (toList "BU_" ++ₗ ' ' ∷ Identifier.name idn ++ₗ ' ' ∷ [])
              (emit attrValueWireFmt wireVal)
              outer-suffix))
      (cong (λ z → toList "BA_ " ++ₗ quoteStringLit-chars n ++ₗ
                     ' ' ∷ 'B' ∷ 'U' ∷ '_' ∷ ' ' ∷ z)
            (++ₗ-assoc (Identifier.name idn) (' ' ∷ [])
                       (emit attrValueWireFmt wireVal ++ₗ
                          ';' ∷ '\n' ∷ outer-suffix))))

emit-attrAssignFmt-RatwMsg :
  ∀ (n : List Char) (raw : ℕ) (wireVal : RawAttrValueWire) →
  emit attrAssignFmt (n , RatwMsg raw , wireVal , tt)
  ≡ toList "BA_ " ++ₗ quoteStringLit-chars n ++ₗ
      ' ' ∷ (toList "BO_" ++ₗ ' ' ∷ emit nat raw ++ₗ ' ' ∷ []) ++ₗ
        (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ [])
emit-attrAssignFmt-RatwMsg _ _ _ = refl

emit-attrAssignFmt-RatwMsg-with-outer :
  ∀ (n : List Char) (raw : ℕ) (wireVal : RawAttrValueWire)
    (outer-suffix : List Char) →
  emit attrAssignFmt (n , RatwMsg raw , wireVal , tt) ++ₗ outer-suffix
  ≡ toList "BA_ " ++ₗ quoteStringLit-chars n ++ₗ
      toList " BO_ " ++ₗ emit nat raw ++ₗ
      ' ' ∷ emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix
emit-attrAssignFmt-RatwMsg-with-outer n raw wireVal outer-suffix =
  trans
    (cong (_++ₗ outer-suffix) (emit-attrAssignFmt-RatwMsg n raw wireVal))
    (trans
      (cong (λ z → toList "BA_ " ++ₗ z)
            (bridge-emit-tail n
              (toList "BO_" ++ₗ ' ' ∷ emit nat raw ++ₗ ' ' ∷ [])
              (emit attrValueWireFmt wireVal)
              outer-suffix))
      (cong (λ z → toList "BA_ " ++ₗ quoteStringLit-chars n ++ₗ
                     ' ' ∷ 'B' ∷ 'O' ∷ '_' ∷ ' ' ∷ z)
            (++ₗ-assoc (emit nat raw) (' ' ∷ [])
                       (emit attrValueWireFmt wireVal ++ₗ
                          ';' ∷ '\n' ∷ outer-suffix))))

emit-attrAssignFmt-RatwSig :
  ∀ (n : List Char) (raw : ℕ) (sig : Identifier) (wireVal : RawAttrValueWire) →
  emit attrAssignFmt (n , RatwSig raw sig , wireVal , tt)
  ≡ toList "BA_ " ++ₗ quoteStringLit-chars n ++ₗ
      ' ' ∷ (toList "SG_" ++ₗ ' ' ∷ (emit nat raw ++ₗ
        ' ' ∷ Identifier.name sig ++ₗ ' ' ∷ [])) ++ₗ
        (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ [])
emit-attrAssignFmt-RatwSig _ _ _ _ = refl

-- Sig: kw-body has nested `(emit nat raw ++ ' ∷ name sig ++ ' ∷ [])` after
-- the SG_ prefix.  Two nested ++-assoc steps to bridge to the canonical
-- spec form `... " SG_ " ++ emit nat raw ++ ' ∷ name sig ++ ' ∷ value-emit
-- ++ ;\n+ outer-suffix`.
emit-attrAssignFmt-RatwSig-with-outer :
  ∀ (n : List Char) (raw : ℕ) (sig : Identifier) (wireVal : RawAttrValueWire)
    (outer-suffix : List Char) →
  emit attrAssignFmt (n , RatwSig raw sig , wireVal , tt) ++ₗ outer-suffix
  ≡ toList "BA_ " ++ₗ quoteStringLit-chars n ++ₗ
      toList " SG_ " ++ₗ emit nat raw ++ₗ
      ' ' ∷ Identifier.name sig ++ₗ
      ' ' ∷ emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix
emit-attrAssignFmt-RatwSig-with-outer n raw sig wireVal outer-suffix =
  trans
    (cong (_++ₗ outer-suffix) (emit-attrAssignFmt-RatwSig n raw sig wireVal))
    (trans
      (cong (λ z → toList "BA_ " ++ₗ z)
            (bridge-emit-tail n
              (toList "SG_" ++ₗ ' ' ∷ (emit nat raw ++ₗ
                ' ' ∷ Identifier.name sig ++ₗ ' ' ∷ []))
              (emit attrValueWireFmt wireVal)
              outer-suffix))
      (cong (λ z → toList "BA_ " ++ₗ quoteStringLit-chars n ++ₗ
                     ' ' ∷ 'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ z)
            (trans
              (++ₗ-assoc (emit nat raw)
                         (' ' ∷ Identifier.name sig ++ₗ ' ' ∷ [])
                         (emit attrValueWireFmt wireVal ++ₗ
                            ';' ∷ '\n' ∷ outer-suffix))
              (cong (λ z → emit nat raw ++ₗ ' ' ∷ z)
                    (++ₗ-assoc (Identifier.name sig) (' ' ∷ [])
                               (emit attrValueWireFmt wireVal ++ₗ
                                  ';' ∷ '\n' ∷ outer-suffix))))))

emit-attrAssignFmt-RatwEv :
  ∀ (n : List Char) (ev : Identifier) (wireVal : RawAttrValueWire) →
  emit attrAssignFmt (n , RatwEv ev , wireVal , tt)
  ≡ toList "BA_ " ++ₗ quoteStringLit-chars n ++ₗ
      ' ' ∷ (toList "EV_" ++ₗ ' ' ∷ Identifier.name ev ++ₗ ' ' ∷ []) ++ₗ
        (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ [])
emit-attrAssignFmt-RatwEv _ _ _ = refl

emit-attrAssignFmt-RatwEv-with-outer :
  ∀ (n : List Char) (ev : Identifier) (wireVal : RawAttrValueWire)
    (outer-suffix : List Char) →
  emit attrAssignFmt (n , RatwEv ev , wireVal , tt) ++ₗ outer-suffix
  ≡ toList "BA_ " ++ₗ quoteStringLit-chars n ++ₗ
      toList " EV_ " ++ₗ Identifier.name ev ++ₗ
      ' ' ∷ emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix
emit-attrAssignFmt-RatwEv-with-outer n ev wireVal outer-suffix =
  trans
    (cong (_++ₗ outer-suffix) (emit-attrAssignFmt-RatwEv n ev wireVal))
    (trans
      (cong (λ z → toList "BA_ " ++ₗ z)
            (bridge-emit-tail n
              (toList "EV_" ++ₗ ' ' ∷ Identifier.name ev ++ₗ ' ' ∷ [])
              (emit attrValueWireFmt wireVal)
              outer-suffix))
      (cong (λ z → toList "BA_ " ++ₗ quoteStringLit-chars n ++ₗ
                     ' ' ∷ 'E' ∷ 'V' ∷ '_' ∷ ' ' ∷ z)
            (++ₗ-assoc (Identifier.name ev) (' ' ∷ [])
                       (emit attrValueWireFmt wireVal ++ₗ
                          ';' ∷ '\n' ∷ outer-suffix))))

-- BA_REL_ line emit equalities.
emit-attrRelFmt-RrtNodeMsg :
  ∀ (n : List Char) (idn : Identifier) (raw : ℕ) (wireVal : RawAttrValueWire) →
  emit attrRelFmt (n , RrtNodeMsg idn raw , wireVal , tt)
  ≡ toList "BA_REL_ " ++ₗ quoteStringLit-chars n ++ₗ
      ' ' ∷ (toList "BU_BO_REL_" ++ₗ ' ' ∷ (Identifier.name idn ++ₗ
        ' ' ∷ emit nat raw ++ₗ ' ' ∷ [])) ++ₗ
        (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ [])
emit-attrRelFmt-RrtNodeMsg _ _ _ _ = refl

-- RrtNodeMsg: kw-body has nested `(name idn ++ ' ∷ emit nat raw ++ ' ∷ [])`
-- after BU_BO_REL_ prefix.  Two nested ++-assoc steps.
emit-attrRelFmt-RrtNodeMsg-with-outer :
  ∀ (n : List Char) (idn : Identifier) (raw : ℕ) (wireVal : RawAttrValueWire)
    (outer-suffix : List Char) →
  emit attrRelFmt (n , RrtNodeMsg idn raw , wireVal , tt) ++ₗ outer-suffix
  ≡ toList "BA_REL_ " ++ₗ quoteStringLit-chars n ++ₗ
      toList " BU_BO_REL_ " ++ₗ Identifier.name idn ++ₗ
      ' ' ∷ emit nat raw ++ₗ
      ' ' ∷ emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix
emit-attrRelFmt-RrtNodeMsg-with-outer n idn raw wireVal outer-suffix =
  trans
    (cong (_++ₗ outer-suffix) (emit-attrRelFmt-RrtNodeMsg n idn raw wireVal))
    (trans
      (cong (λ z → toList "BA_REL_ " ++ₗ z)
            (bridge-emit-tail n
              (toList "BU_BO_REL_" ++ₗ ' ' ∷ (Identifier.name idn ++ₗ
                ' ' ∷ emit nat raw ++ₗ ' ' ∷ []))
              (emit attrValueWireFmt wireVal)
              outer-suffix))
      (cong (λ z → toList "BA_REL_ " ++ₗ quoteStringLit-chars n ++ₗ
                     ' ' ∷ 'B' ∷ 'U' ∷ '_' ∷ 'B' ∷ 'O' ∷ '_' ∷
                       'R' ∷ 'E' ∷ 'L' ∷ '_' ∷ ' ' ∷ z)
            (trans
              (++ₗ-assoc (Identifier.name idn)
                         (' ' ∷ emit nat raw ++ₗ ' ' ∷ [])
                         (emit attrValueWireFmt wireVal ++ₗ
                            ';' ∷ '\n' ∷ outer-suffix))
              (cong (λ z → Identifier.name idn ++ₗ ' ' ∷ z)
                    (++ₗ-assoc (emit nat raw) (' ' ∷ [])
                               (emit attrValueWireFmt wireVal ++ₗ
                                  ';' ∷ '\n' ∷ outer-suffix))))))

emit-attrRelFmt-RrtNodeSig :
  ∀ (n : List Char) (idn : Identifier) (raw : ℕ) (sig : Identifier)
    (wireVal : RawAttrValueWire) →
  emit attrRelFmt (n , RrtNodeSig idn raw sig , wireVal , tt)
  ≡ toList "BA_REL_ " ++ₗ quoteStringLit-chars n ++ₗ
      ' ' ∷ (toList "BU_SG_REL_" ++ₗ ' ' ∷ (Identifier.name idn ++ₗ
        ' ' ∷ (toList "SG_" ++ₗ ' ' ∷ (emit nat raw ++ₗ
          ' ' ∷ Identifier.name sig ++ₗ ' ' ∷ [])))) ++ₗ
        (emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ [])
emit-attrRelFmt-RrtNodeSig _ _ _ _ _ = refl

-- RrtNodeSig: most nested kw-body — three nested ++-assoc steps.
emit-attrRelFmt-RrtNodeSig-with-outer :
  ∀ (n : List Char) (idn : Identifier) (raw : ℕ) (sig : Identifier)
    (wireVal : RawAttrValueWire) (outer-suffix : List Char) →
  emit attrRelFmt (n , RrtNodeSig idn raw sig , wireVal , tt) ++ₗ outer-suffix
  ≡ toList "BA_REL_ " ++ₗ quoteStringLit-chars n ++ₗ
      toList " BU_SG_REL_ " ++ₗ Identifier.name idn ++ₗ
      ' ' ∷ toList "SG_ " ++ₗ emit nat raw ++ₗ
      ' ' ∷ Identifier.name sig ++ₗ
      ' ' ∷ emit attrValueWireFmt wireVal ++ₗ ';' ∷ '\n' ∷ outer-suffix
emit-attrRelFmt-RrtNodeSig-with-outer n idn raw sig wireVal outer-suffix =
  trans
    (cong (_++ₗ outer-suffix) (emit-attrRelFmt-RrtNodeSig n idn raw sig wireVal))
    (trans
      (cong (λ z → toList "BA_REL_ " ++ₗ z)
            (bridge-emit-tail n
              (toList "BU_SG_REL_" ++ₗ ' ' ∷ (Identifier.name idn ++ₗ
                ' ' ∷ (toList "SG_" ++ₗ ' ' ∷ (emit nat raw ++ₗ
                  ' ' ∷ Identifier.name sig ++ₗ ' ' ∷ []))))
              (emit attrValueWireFmt wireVal)
              outer-suffix))
      (cong (λ z → toList "BA_REL_ " ++ₗ quoteStringLit-chars n ++ₗ
                     ' ' ∷ 'B' ∷ 'U' ∷ '_' ∷ 'S' ∷ 'G' ∷ '_' ∷
                       'R' ∷ 'E' ∷ 'L' ∷ '_' ∷ ' ' ∷ z)
            (trans
              (++ₗ-assoc (Identifier.name idn)
                         (' ' ∷ (toList "SG_" ++ₗ ' ' ∷ (emit nat raw ++ₗ
                           ' ' ∷ Identifier.name sig ++ₗ ' ' ∷ [])))
                         (emit attrValueWireFmt wireVal ++ₗ
                            ';' ∷ '\n' ∷ outer-suffix))
              (cong (λ z → Identifier.name idn ++ₗ
                              ' ' ∷ 'S' ∷ 'G' ∷ '_' ∷ ' ' ∷ z)
                    (trans
                      (++ₗ-assoc (emit nat raw)
                                 (' ' ∷ Identifier.name sig ++ₗ ' ' ∷ [])
                                 (emit attrValueWireFmt wireVal ++ₗ
                                    ';' ∷ '\n' ∷ outer-suffix))
                      (cong (λ z → emit nat raw ++ₗ ' ' ∷ z)
                            (++ₗ-assoc (Identifier.name sig) (' ' ∷ [])
                                       (emit attrValueWireFmt wireVal ++ₗ
                                          ';' ∷ '\n' ∷ outer-suffix))))))))

-- ============================================================================
-- KEYWORD-TARGET L5 BUILDERS — `EmitsOK stdTargetWireFmt (RatwXxx ...) suffix`
-- ============================================================================
--
-- For keyword targets, L5 reduces (via iso → 4 inj₁ peels through the
-- 5-way altSum) to `EmitsOK <kwArm> body suffix`.  No top-level
-- disjointness obligation (those only apply to the inj₂ empty-arm
-- fall-through, i.e. RatwNet).  The structural EmitsOK pieces are
-- assembled directly from per-shape preconditions (head-stop witnesses
-- + suffix-stop on the value-emit slot).

-- For nodeArm / evArm: `pair (literal "<KW>_") (withWS (pair ident ws))`.
-- The L5.2 slot reduces to `SuffixStops isHSpace ((Identifier.name idn
-- ++ ' ' ∷ []) ++ suffix)` — the `(name ++ ' ∷ [])` is the left-assoc
-- output of `emit identTrailingWS idn`, NOT the right-assoc `name ++ ' ∷
-- suffix` form.  Caller must supply this exact shape (constructed via
-- ++-assoc subst from the IdentNameStop head witness).
--
-- Disjointness: `bwdStdTgt`'s inj-position determines what altSum
-- disjointness obligations are needed at the L5.0 (outermost) level:
--   * RatwNode (inj₁₄)         : 0 obligations (innermost inj₁ throughout)
--   * RatwMsg  (inj₁₃ + inj₂₁) : 1 obligation against `nodeArm`
--   * RatwSig  (inj₁₂ + inj₂₁) : 1 obligation against `altSum nodeArm msgArm`
--   * RatwEv   (inj₁  + inj₂)  : 1 obligation against
--                                `altSum (altSum nodeArm msgArm) sigArm`
-- Each disjointness closes by `λ _ → refl` on closed-Char first-char
-- mismatch (Msg's "BO_" vs "BU_" mismatches on second char, etc.).

build-EmitsOK-stdTargetWireFmt-RatwNode :
  ∀ (idn : Identifier) (suffix : List Char)
  → SuffixStops isHSpace ((Identifier.name idn ++ₗ ' ' ∷ []) ++ₗ suffix)
  → SuffixStops isHSpace suffix
  → EmitsOK stdTargetWireFmt (RatwNode idn) suffix
build-EmitsOK-stdTargetWireFmt-RatwNode idn suffix name-stop val-stop =
  tt , name-stop , ∷-stop refl , val-stop

build-EmitsOK-stdTargetWireFmt-RatwEv :
  ∀ (ev : Identifier) (suffix : List Char)
  → SuffixStops isHSpace ((Identifier.name ev ++ₗ ' ' ∷ []) ++ₗ suffix)
  → SuffixStops isHSpace suffix
  → EmitsOK stdTargetWireFmt (RatwEv ev) suffix
build-EmitsOK-stdTargetWireFmt-RatwEv ev suffix name-stop val-stop =
  ((tt , name-stop , ∷-stop refl , val-stop) , λ _ → refl)

-- For msgArm: `pair (literal "BO_") (withWS (pair nat ws))`.  Closed via
-- showNat-chars-head — first digit is non-hspace, no caller witness needed.
-- Disjointness against nodeArm closes by `λ _ → refl` (BO_ vs BU_ on 2nd char).
build-EmitsOK-stdTargetWireFmt-RatwMsg :
  ∀ (raw : ℕ) (suffix : List Char)
  → SuffixStops isHSpace suffix
  → EmitsOK stdTargetWireFmt (RatwMsg raw) suffix
build-EmitsOK-stdTargetWireFmt-RatwMsg raw suffix val-stop =
  ((tt , raw-stop , ∷-stop refl , val-stop) , λ _ → refl)
  where
    raw-stop : SuffixStops isHSpace ((emit nat raw ++ₗ ' ' ∷ []) ++ₗ suffix)
    raw-stop with showNat-chars-head raw
    ... | d , tail , d<10 , eq =
      subst (λ chars → SuffixStops isHSpace ((chars ++ₗ ' ' ∷ []) ++ₗ suffix))
            (sym eq) (∷-stop (digit-not-isHSpace d))

-- For sigArm: `pair (literal "SG_") (withWS (pair nat (withWS (pair ident
-- ws))))`.  Disjointness against `altSum nodeArm msgArm` closes by `λ _ →
-- refl` (SG_ vs B*_ on first char).
build-EmitsOK-stdTargetWireFmt-RatwSig :
  ∀ (raw : ℕ) (sig : Identifier) (suffix : List Char)
  → SuffixStops isHSpace ((Identifier.name sig ++ₗ ' ' ∷ []) ++ₗ suffix)
  → SuffixStops isHSpace suffix
  → EmitsOK stdTargetWireFmt (RatwSig raw sig) suffix
build-EmitsOK-stdTargetWireFmt-RatwSig raw sig suffix sig-stop val-stop =
  ((tt , raw-stop ,
    (∷-stop refl , (sig-stop , (∷-stop refl , val-stop)))) ,
   λ _ → refl)
  where
    raw-stop : SuffixStops isHSpace
      ((emit nat raw ++ₗ
        ' ' ∷ ((Identifier.name sig ++ₗ ' ' ∷ []))) ++ₗ suffix)
    raw-stop with showNat-chars-head raw
    ... | d , tail , d<10 , eq =
      subst (λ chars → SuffixStops isHSpace
                ((chars ++ₗ ' ' ∷ ((Identifier.name sig ++ₗ ' ' ∷ [])))
                  ++ₗ suffix))
            (sym eq) (∷-stop (digit-not-isHSpace d))

-- For nodeMsgArm: `pair (literal "BU_BO_REL_") (withWS (pair ident (withWS
-- (pair nat ws))))`.  L5 inputs: idn IdentNameStop (over the longer span),
-- raw via showNat, val-stop.
build-EmitsOK-relTargetWireFmt-RrtNodeMsg :
  ∀ (idn : Identifier) (raw : ℕ) (suffix : List Char)
  → SuffixStops isHSpace
      ((Identifier.name idn ++ₗ ' ' ∷ ((emit nat raw ++ₗ ' ' ∷ []))) ++ₗ suffix)
  → SuffixStops isHSpace suffix
  → EmitsOK relTargetWireFmt (RrtNodeMsg idn raw) suffix
build-EmitsOK-relTargetWireFmt-RrtNodeMsg idn raw suffix idn-stop val-stop =
  tt , idn-stop , (∷-stop refl , (raw-stop , (∷-stop refl , val-stop)))
  where
    raw-stop : SuffixStops isHSpace ((emit nat raw ++ₗ ' ' ∷ []) ++ₗ suffix)
    raw-stop with showNat-chars-head raw
    ... | d , tail , d<10 , eq =
      subst (λ chars → SuffixStops isHSpace ((chars ++ₗ ' ' ∷ []) ++ₗ suffix))
            (sym eq) (∷-stop (digit-not-isHSpace d))

-- RrtNodeSig is the inj₂ position of `altSum nodeMsgArm nodeSigArm`, so
-- needs disjointness against nodeMsgArm.  nodeMsgArm prefix is
-- "BU_BO_REL_"; nodeSigArm prefix is "BU_SG_REL_" — differ at index 3
-- (`B` vs `S`).  parse nodeMsgArm pos input fails on 4th-char mismatch
-- once the leading `BU_` matches; closes by `λ _ → refl`.
build-EmitsOK-relTargetWireFmt-RrtNodeSig :
  ∀ (idn : Identifier) (raw : ℕ) (sig : Identifier) (suffix : List Char)
  → SuffixStops isHSpace
      ((Identifier.name idn ++ₗ ' ' ∷
        ((toList "SG_" ++ₗ ' ' ∷ ((emit nat raw ++ₗ
          ' ' ∷ ((Identifier.name sig ++ₗ ' ' ∷ []))))))) ++ₗ suffix)
  → SuffixStops isHSpace ((Identifier.name sig ++ₗ ' ' ∷ []) ++ₗ suffix)
  → SuffixStops isHSpace suffix
  → EmitsOK relTargetWireFmt (RrtNodeSig idn raw sig) suffix
build-EmitsOK-relTargetWireFmt-RrtNodeSig idn raw sig suffix idn-stop sig-stop val-stop =
  ((tt , idn-stop , (∷-stop refl ,
    (∷-stop refl ,
     (tt , (raw-stop , (∷-stop refl , (sig-stop , (∷-stop refl , val-stop))))))))
   , λ _ → refl)
  where
    raw-stop : SuffixStops isHSpace
      ((emit nat raw ++ₗ
        ' ' ∷ ((Identifier.name sig ++ₗ ' ' ∷ []))) ++ₗ suffix)
    raw-stop with showNat-chars-head raw
    ... | d , tail , d<10 , eq =
      subst (λ chars → SuffixStops isHSpace
                ((chars ++ₗ ' ' ∷ ((Identifier.name sig ++ₗ ' ' ∷ [])))
                  ++ₗ suffix))
            (sym eq) (∷-stop (digit-not-isHSpace d))
