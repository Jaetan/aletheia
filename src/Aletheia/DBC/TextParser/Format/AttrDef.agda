{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.5.d 3c-A — DSL-side Formats for the BA_DEF_ /
-- BA_DEF_REL_ attribute-definition lines.
--
-- Grammar slice (mirrors `TextParser.Attributes`):
--   attr-def     ::= "BA_DEF_" ws (attr-scope ws)? string-lit ws attr-type
--                    ws? ";" newline
--   attr-def-rel ::= "BA_DEF_REL_" ws rel-scope ws string-lit ws attr-type
--                    ws? ";" newline
--   attr-scope   ::= "BU_" | "BO_" | "SG_" | "EV_"          (4-way)
--   rel-scope    ::= "BU_BO_REL_" | "BU_SG_REL_"            (2-way)
--   attr-type    ::= "STRING" | "INT" ws int ws int
--                  | "FLOAT" ws decRat ws decRat
--                  | "ENUM" ws string-lit ("," ws? string-lit)*
--                  | "HEX" ws nat ws nat                    (5-way)
--
-- Raw-ADT-in-Format pattern (3d.8 messageHeaderFmt / CM_ precedent):
-- the Format DSL produces a `Raw` intermediate keeping the ENUM cons split
-- (`RatEnum h t`) and the scope-vs-rel-scope split (`RawStdScope` /
-- `RawRelScope`); wrappers `liftStdAttrDef` / `liftRelAttrDef` lift to the
-- AST `AttrDef` (always total — every Raw value corresponds to a valid
-- AttrDef).
--
-- The trailing `many parseNewline` consumption (zero-or-more blank lines
-- after the line terminator) lives in the production wrapper, NOT in this
-- Format — same pattern as `Format/ValueTable.agda` / `Format/EnvVar.agda`.
-- The Format itself emits exactly one `\n` via `newlineFmt`.
module Aletheia.DBC.TextParser.Format.AttrDef where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char; _≈ᵇ_)
open import Data.Char.Base using (isDigit)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_) renaming (_++_ to _++ₗ_)
open import Data.List.Properties using () renaming (++-assoc to ++ₗ-assoc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; Σ-syntax)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; trans; subst)

open import Aletheia.Parser.Combinators
  using (Position; Parser; ParseResult; mkResult; advancePositions)
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.DecRat using (DecRat; mkDecRat)
open import Aletheia.DBC.DecRat.Refinement using
  (IntDecRat; intDecRatToℤ; NatDecRat; natDecRatToℕ)
open import Aletheia.DBC.Types using
  ( AttrScope; ASNetwork; ASNode; ASMessage; ASSignal; ASEnvVar
  ; ASNodeMsg; ASNodeSig
  ; AttrType; ATInt; ATFloat; ATString; ATEnum; ATHex
  ; AttrDef; mkAttrDef)
open import Aletheia.DBC.TextParser.Lexer using (isHSpace)
open import Aletheia.DBC.TextFormatter.Emitter
  using (digitChar; showInt-chars; showNat-chars; showDecRat-dec-chars;
         quoteStringLit-chars)
open import Aletheia.DBC.TextFormatter.Attributes using
  (emitAttrDef-chars; emitAttrType-chars; emitEnumLabels-chars;
   emitScopePrefix-chars; isRelScope)
open import Aletheia.DBC.TextParser.DecRatParse.Properties
  using (SuffixStops; ∷-stop; headOr;
         showNat-chars-head;
         showDecRat-chars-head-dash; showDecRat-chars-head-digit)
open import Aletheia.DBC.TextParser.Properties.Primitives
  using (quoteStringLit-chars-shape)
open import Aletheia.DBC.TextParser.Format
  using (Format; literal; ident; nat; stringLit; pair; iso; many;
         altSum; ws; wsOpt; wsCanonOne; decRat; intDecRat; natDecRat;
         withPrefix; emit; parse; EmitsOK; ParseFailsAt; roundtrip)

-- ============================================================================
-- LOCAL SUGAR — ws-aware combinators (mirrors Format/EnvVar / Format/Comments)
-- ============================================================================

private
  -- Mandatory single space, parser one-or-more.  Canonical emit `' ' ∷ []`.
  withWS : ∀ {A} → Format A → Format A
  withWS f = iso proj₂ (λ a → tt , a) (λ _ → refl) (pair ws f)

  -- Optional whitespace, parser zero-or-more.  Canonical emit `[]`.
  withWSOpt : ∀ {A} → Format A → Format A
  withWSOpt f = iso proj₂ (λ a → tt , a) (λ _ → refl) (pair wsOpt f)

  -- Canonical-single-space, parser zero-or-more.  Canonical emit `' ' ∷ []`.
  -- Used at the trailing `parseWSOpt` slot before `;` where the formatter
  -- emits exactly one space.
  withWSCanonOne : ∀ {A} → Format A → Format A
  withWSCanonOne f = iso proj₂ (λ a → tt , a) (λ _ → refl) (pair wsCanonOne f)

  -- Line terminator: accepts `"\r\n"` or `"\n"`, canonical emit `"\n"`.
  newlineFmt : Format ⊤
  newlineFmt = iso (λ _ → tt) (λ _ → inj₂ tt) (λ _ → refl)
                    (altSum (literal ('\r' ∷ '\n' ∷ []))
                            (literal ('\n' ∷ [])))

-- ============================================================================
-- RAW SCOPE / TYPE ADTs
-- ============================================================================

-- Standard scope (5 cases — for BA_DEF_).
data RawStdScope : Set where
  RssNet  : RawStdScope
  RssNode : RawStdScope
  RssMsg  : RawStdScope
  RssSig  : RawStdScope
  RssEnv  : RawStdScope

-- Relation scope (2 cases — for BA_DEF_REL_).
data RawRelScope : Set where
  RrsNodeMsg : RawRelScope
  RrsNodeSig : RawRelScope

-- Attribute type, ENUM-cons-required.  `RatEnum h t` represents `ATEnum
-- (h ∷ t)`; `ATEnum []` has no representation in the raw type (rejected
-- by the existing parser anyway: parseEnumLabels requires at least one
-- string literal).
data RawAttrType : Set where
  RatString : RawAttrType
  RatInt    : IntDecRat → IntDecRat → RawAttrType
  RatFloat  : DecRat    → DecRat    → RawAttrType
  RatEnum   : List Char → List (List Char) → RawAttrType
  RatHex    : NatDecRat → NatDecRat → RawAttrType

-- Lifters from raw → AST.  All total.

liftStdScope : RawStdScope → AttrScope
liftStdScope RssNet  = ASNetwork
liftStdScope RssNode = ASNode
liftStdScope RssMsg  = ASMessage
liftStdScope RssSig  = ASSignal
liftStdScope RssEnv  = ASEnvVar

liftRelScope : RawRelScope → AttrScope
liftRelScope RrsNodeMsg = ASNodeMsg
liftRelScope RrsNodeSig = ASNodeSig

liftAttrType : RawAttrType → AttrType
liftAttrType RatString       = ATString
liftAttrType (RatInt mn mx)  = ATInt mn mx
liftAttrType (RatFloat mn mx) = ATFloat mn mx
liftAttrType (RatEnum h t)   = ATEnum (h ∷ t)
liftAttrType (RatHex mn mx)  = ATHex mn mx

-- ============================================================================
-- ATTRIBUTE TYPE FORMAT — 5-way altSum + iso
-- ============================================================================

-- INT arm carrier: pair of IntDecRat with mandatory single space between.
-- Wire: `INT ws <int1> ws <int2>`.
private
  intArm : Format (IntDecRat × IntDecRat)
  intArm = withPrefix (toList "INT") (withWS (pair intDecRat (withWS intDecRat)))

  -- FLOAT arm: pair of DecRat with mandatory single space between.
  -- Wire: `FLOAT ws <dec1> ws <dec2>`.
  floatArm : Format (DecRat × DecRat)
  floatArm = withPrefix (toList "FLOAT") (withWS (pair decRat (withWS decRat)))

  -- HEX arm: pair of NatDecRat with mandatory single space between.
  -- Wire: `HEX ws <nat1> ws <nat2>`.
  hexArm : Format (NatDecRat × NatDecRat)
  hexArm = withPrefix (toList "HEX") (withWS (pair natDecRat (withWS natDecRat)))

  -- ENUM arm: head label + tail labels (cons-required).
  -- Wire: `ENUM ws <head>("," wsOpt <label>)*`.  The DSL's `many` over
  -- `withPrefix "," (withWSOpt stringLit)` matches the parser's
  -- `many (char ',' *> parseWSOpt *> parseStringLit)`; canonical emit
  -- has empty `wsOpt` so `,<label>,<label>` (no spaces around commas)
  -- aligns with `emitEnumLabels-chars`.
  enumArm : Format (List Char × List (List Char))
  enumArm =
    withPrefix (toList "ENUM") (
      withWS (
        pair stringLit (
          many (withPrefix (',' ∷ []) (withWSOpt stringLit)))))

  -- STRING arm: keyword only, no body.  Carrier `⊤`.
  stringArm : Format ⊤
  stringArm = literal (toList "STRING")

  -- Underlying altSum carrier: 5-way left-associated nested ⊎.
  -- Order matches the existing `parseAttrTypeDecl` precedence:
  --     STRING <|> INT <|> FLOAT <|> ENUM <|> HEX
  -- Each keyword's first char is distinct (S/I/F/E/H), so altSum
  -- disjointness reduces to per-keyword char-mismatch refl proofs.
  AttrTypeCarrier : Set
  AttrTypeCarrier =
    ⊤ ⊎ ((IntDecRat × IntDecRat) ⊎ ((DecRat × DecRat) ⊎
      ((List Char × List (List Char)) ⊎ (NatDecRat × NatDecRat))))

  attrTypeCarrierFmt : Format AttrTypeCarrier
  attrTypeCarrierFmt =
    altSum stringArm (
      altSum intArm (
        altSum floatArm (
          altSum enumArm hexArm)))

  fwdRat : AttrTypeCarrier → RawAttrType
  fwdRat (inj₁ tt)                              = RatString
  fwdRat (inj₂ (inj₁ (mn , mx)))                 = RatInt mn mx
  fwdRat (inj₂ (inj₂ (inj₁ (mn , mx))))          = RatFloat mn mx
  fwdRat (inj₂ (inj₂ (inj₂ (inj₁ (h , t)))))     = RatEnum h t
  fwdRat (inj₂ (inj₂ (inj₂ (inj₂ (mn , mx)))))   = RatHex mn mx

  bwdRat : RawAttrType → AttrTypeCarrier
  bwdRat RatString       = inj₁ tt
  bwdRat (RatInt mn mx)  = inj₂ (inj₁ (mn , mx))
  bwdRat (RatFloat mn mx) = inj₂ (inj₂ (inj₁ (mn , mx)))
  bwdRat (RatEnum h t)   = inj₂ (inj₂ (inj₂ (inj₁ (h , t))))
  bwdRat (RatHex mn mx)  = inj₂ (inj₂ (inj₂ (inj₂ (mn , mx))))

  fwdRat-bwdRat : ∀ rt → fwdRat (bwdRat rt) ≡ rt
  fwdRat-bwdRat RatString       = refl
  fwdRat-bwdRat (RatInt _ _)    = refl
  fwdRat-bwdRat (RatFloat _ _)  = refl
  fwdRat-bwdRat (RatEnum _ _)   = refl
  fwdRat-bwdRat (RatHex _ _)    = refl

attrTypeFmt : Format RawAttrType
attrTypeFmt = iso fwdRat bwdRat fwdRat-bwdRat attrTypeCarrierFmt

-- ============================================================================
-- SCOPE FORMATS
-- ============================================================================

-- Standard scope dispatch.  ASNetwork emits `[]` (no scope keyword);
-- ASNode/Msg/Sig/EnvVar emit their keyword + trailing space.
--
-- Wire alignment: `parseOptionalStandardScope = (parseStandardScope <*
-- parseWS) <|> pure ASNetwork`.  The 4-keyword arm matches `BU_`/`BO_`/
-- `SG_`/`EV_` then consumes whitespace; the empty arm produces ASNetwork
-- with zero consumption.  In the DSL: 4 `withPrefix <kw> ws` arms (each
-- with carrier `⊤`) joined by altSum, with a `literal []` empty arm.
private
  StdScopeCarrier : Set
  StdScopeCarrier = ((((⊤ ⊎ ⊤) ⊎ ⊤) ⊎ ⊤) ⊎ ⊤)
  -- ((((BU_ ⊎ BO_) ⊎ SG_) ⊎ EV_) ⊎ Network)

  stdScopeCarrierFmt : Format StdScopeCarrier
  stdScopeCarrierFmt =
    altSum (
      altSum (
        altSum (
          altSum
            (withPrefix (toList "BU_") ws)         -- ASNode
            (withPrefix (toList "BO_") ws))        -- ASMessage
          (withPrefix (toList "SG_") ws))          -- ASSignal
        (withPrefix (toList "EV_") ws))            -- ASEnvVar
      (literal [])                                  -- ASNetwork (empty emit)

  fwdStd : StdScopeCarrier → RawStdScope
  fwdStd (inj₁ (inj₁ (inj₁ (inj₁ tt)))) = RssNode
  fwdStd (inj₁ (inj₁ (inj₁ (inj₂ tt)))) = RssMsg
  fwdStd (inj₁ (inj₁ (inj₂ tt)))         = RssSig
  fwdStd (inj₁ (inj₂ tt))                 = RssEnv
  fwdStd (inj₂ tt)                         = RssNet

  bwdStd : RawStdScope → StdScopeCarrier
  bwdStd RssNode = inj₁ (inj₁ (inj₁ (inj₁ tt)))
  bwdStd RssMsg  = inj₁ (inj₁ (inj₁ (inj₂ tt)))
  bwdStd RssSig  = inj₁ (inj₁ (inj₂ tt))
  bwdStd RssEnv  = inj₁ (inj₂ tt)
  bwdStd RssNet  = inj₂ tt

  fwdStd-bwdStd : ∀ s → fwdStd (bwdStd s) ≡ s
  fwdStd-bwdStd RssNet  = refl
  fwdStd-bwdStd RssNode = refl
  fwdStd-bwdStd RssMsg  = refl
  fwdStd-bwdStd RssSig  = refl
  fwdStd-bwdStd RssEnv  = refl

stdScopeFmt : Format RawStdScope
stdScopeFmt = iso fwdStd bwdStd fwdStd-bwdStd stdScopeCarrierFmt

-- Relation scope dispatch.  No empty arm — `BU_BO_REL_` or `BU_SG_REL_`
-- mandatory.  Trailing whitespace consumed by the keyword's `ws`.
private
  RelScopeCarrier : Set
  RelScopeCarrier = ⊤ ⊎ ⊤
  -- (BU_BO_REL_ ⊎ BU_SG_REL_)

  relScopeCarrierFmt : Format RelScopeCarrier
  relScopeCarrierFmt =
    altSum
      (literal (toList "BU_BO_REL_"))                  -- ASNodeMsg
      (literal (toList "BU_SG_REL_"))                  -- ASNodeSig

  fwdRel : RelScopeCarrier → RawRelScope
  fwdRel (inj₁ tt) = RrsNodeMsg
  fwdRel (inj₂ tt) = RrsNodeSig

  bwdRel : RawRelScope → RelScopeCarrier
  bwdRel RrsNodeMsg = inj₁ tt
  bwdRel RrsNodeSig = inj₂ tt

  fwdRel-bwdRel : ∀ s → fwdRel (bwdRel s) ≡ s
  fwdRel-bwdRel RrsNodeMsg = refl
  fwdRel-bwdRel RrsNodeSig = refl

relScopeFmt : Format RawRelScope
relScopeFmt = iso fwdRel bwdRel fwdRel-bwdRel relScopeCarrierFmt

-- ============================================================================
-- LINE FORMATS
-- ============================================================================

-- Carrier shape: each line carries (scope, name, type, ⊤-trailing).  The
-- trailing `⊤` is the result of the `wsCanonOne; ";"; newline` chain.
StdAttrDefCarrier : Set
StdAttrDefCarrier = RawStdScope × (List Char × (RawAttrType × ⊤))

RelAttrDefCarrier : Set
RelAttrDefCarrier = RawRelScope × (List Char × (RawAttrType × ⊤))

-- BA_DEF_ line.  Wire shape:
--     BA_DEF_ <scope-prefix><"name"> <type> ;\n
-- where `<scope-prefix>` is `[]` for ASNetwork or `BU_ `/`BO_ `/`SG_ `/
-- `EV_ ` for the four standard scopes (the trailing space is consumed by
-- `stdScopeFmt`'s per-keyword `ws`).
attrDefFmt : Format StdAttrDefCarrier
attrDefFmt =
  withPrefix (toList "BA_DEF_") (
    withWS (
      pair stdScopeFmt (
        pair stringLit (
          withWS (
            pair attrTypeFmt (
              withWSCanonOne (
                withPrefix (';' ∷ []) newlineFmt)))))))

-- BA_DEF_REL_ line.  Wire shape:
--     BA_DEF_REL_ <"BU_BO_REL_"|"BU_SG_REL_"> <"name"> <type> ;\n
-- with mandatory single space between every token.  Unlike `attrDefFmt`
-- (where the std-scope keyword bakes the trailing space into its arm
-- via `withPrefix "BU_" ws`), the rel-scope keyword is just the literal
-- and the trailing-space-before-name is supplied by an explicit `withWS`
-- between `relScopeFmt` and `stringLit`.  This mirrors the parser's
-- structure: `parseRelScope` consumes only the keyword, then
-- `parseAttrDefRel` runs an explicit `parseWS` before `parseStringLit`.
attrDefRelFmt : Format RelAttrDefCarrier
attrDefRelFmt =
  withPrefix (toList "BA_DEF_REL_") (
    withWS (
      pair relScopeFmt (
        withWS (
          pair stringLit (
            withWS (
              pair attrTypeFmt (
                withWSCanonOne (
                  withPrefix (';' ∷ []) newlineFmt))))))))

-- ============================================================================
-- AST LIFTERS
-- ============================================================================

-- Build an `AttrDef` from a Std-scope raw line carrier.
liftStdAttrDef : StdAttrDefCarrier → AttrDef
liftStdAttrDef (s , n , t , _) =
  mkAttrDef n (liftStdScope s) (liftAttrType t)

-- Build an `AttrDef` from a Rel-scope raw line carrier.
liftRelAttrDef : RelAttrDefCarrier → AttrDef
liftRelAttrDef (s , n , t , _) =
  mkAttrDef n (liftRelScope s) (liftAttrType t)

-- ============================================================================
-- HEAD-NON-HSPACE HELPERS
-- ============================================================================

-- The bridges from emit shape to `SuffixStops isHSpace …` preconditions
-- typically need the head of `emit X v ++ rest` to be a non-hspace char.
-- For closed prefixes (`literal "BU_"` etc.) the head is the first
-- closed-Char letter.  These helpers cover the data-dependent leaves
-- (showInt/showNat/showDecRat heads + stringLit's leading `'"'`).

private
  -- 10 digit chars are non-hspace.  `digitChar d` for any closed `d` is
  -- in {'0' … '9'}; closed-char `≈ᵇ` comparison reduces to `false` for
  -- both space (' ') and tab ('\t').
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

  -- Head of `(showNat-chars n ++ inner-rest) ++ outer-suffix` is non-hspace.
  -- Mirrors `Format/Comments.agda`'s `showNat-chars-head-non-hspace`.
  showNat-chars-head-stop : ∀ (n : ℕ) (rest : List Char)
    → SuffixStops isHSpace (showNat-chars n ++ₗ rest)
  showNat-chars-head-stop n rest with showNat-chars-head n
  ... | d , tail , _ , eq =
        subst (λ xs → SuffixStops isHSpace (xs ++ₗ rest))
              (sym eq)
              (∷-stop (digit-not-isHSpace d))

  -- Head of `(showInt-chars z ++ inner-rest) ++ outer-suffix` is non-hspace.
  -- Three-case dispatch: `(+ zero)` / `(+ suc n)` / `-[1+ _ ]` (the
  -- `-` head is non-hspace by `refl`).
  showInt-chars-head-stop : ∀ (z : ℤ) (rest : List Char)
    → SuffixStops isHSpace (showInt-chars z ++ₗ rest)
  showInt-chars-head-stop (+ n) rest = showNat-chars-head-stop n rest
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

  -- Head of `(quoteStringLit-chars cs ++ inner-rest) ++ outer-suffix` is
  -- `'"'` (non-hspace).  `quoteStringLit-chars` always starts with `'"'`
  -- by definitional reduction.
  quoted-head-stop : ∀ (cs rest : List Char)
    → SuffixStops isHSpace (quoteStringLit-chars cs ++ₗ rest)
  quoted-head-stop _ _ = ∷-stop refl

  -- `'.' ≢ headOr (' ' ∷ rest) '_'` discharges by `λ ()` — `headOr`
  -- returns the first elem when non-empty, so `headOr (' ' ∷ rest) _ = ' '`
  -- and `'.' ≡ ' '` is absurd.
  not-dot-after-space : ∀ (rest : List Char)
    → '.' ≢ headOr (' ' ∷ rest) '_'
  not-dot-after-space _ = λ ()

  -- ++ₗ-assoc bridge: convert a right-associated `xs ++ (as ++ bs)`
  -- SuffixStops witness to the left-associated `(xs ++ as) ++ bs`
  -- shape required by EmitsOK reductions of `withWS (pair intDecRat
  -- (withWS intDecRat))` etc.  `withWS f`'s emit is `' ' ∷ emit f a`,
  -- and `pair g h`'s emit is `emit g a ++ emit h b`, so the suffix at
  -- the leading-ws slot is `(emit g a ++ emit h b) ++ outer-suffix` —
  -- left-associated.  Our `showXxx-chars-head-stop` helpers produce a
  -- right-associated witness; this bridges them.
  assoc-bridgeᴴ : ∀ (xs as bs : List Char)
    → SuffixStops isHSpace (xs ++ₗ (as ++ₗ bs))
    → SuffixStops isHSpace ((xs ++ₗ as) ++ₗ bs)
  assoc-bridgeᴴ xs as bs ss =
    subst (SuffixStops isHSpace) (sym (++ₗ-assoc xs as bs)) ss

  assoc-bridgeᴰ : ∀ (xs as bs : List Char)
    → SuffixStops isDigit (xs ++ₗ (as ++ₗ bs))
    → SuffixStops isDigit ((xs ++ₗ as) ++ₗ bs)
  assoc-bridgeᴰ xs as bs ss =
    subst (SuffixStops isDigit) (sym (++ₗ-assoc xs as bs)) ss

-- ============================================================================
-- EMITS-OK BUILDERS — concrete-shape preconditions baked into signatures
-- ============================================================================
--
-- Per advisor (3d.5.d 3c-A): the production use site has the suffix at
-- `attrTypeFmt`'s slot as `' ' ∷ ';' ∷ '\n' ∷ outer-line-suffix` (from
-- the trailing `withWSCanonOne (withPrefix ";" newlineFmt)`), and at
-- `stdScopeFmt`/`relScopeFmt`'s slot as `quoteStringLit-chars name ++
-- rest` (head `'"'`, from the immediately following `pair stringLit
-- ...`).  Bake these concrete shapes into the builder signatures so
-- every inner SuffixStops witness closes by `refl` on the closed-Char
-- head, and altSum disjointness witnesses close by `λ _ → refl` (the
-- earlier alt's keyword first-char differs from the actual head).

-- Standard scope: at the call site in `attrDefFmt`, the suffix is
-- `(quoteStringLit-chars name ++ inner) ++ outer-suffix` where inner
-- is the emit of the trailing `withWS (pair attrTypeFmt (...))` chunk.
-- Bake the left-associated `(_ ++ _) ++ _` shape so all inner SuffixStops
-- witnesses close by `∷-stop refl` on the closed `'"'` head (folded
-- through the leading `'"' ∷` of `quoteStringLit-chars`).  altSum
-- disjointness witnesses against earlier alts close by `λ _ → refl`
-- since each keyword's first char differs from `'"'`.
--
-- For the rel scope (used in `attrDefRelFmt`), the call-site suffix has
-- an extra leading space (from the explicit `withWS` between
-- `relScopeFmt` and `stringLit`).  Since `relScopeFmt`'s inner reductions
-- only check the leading-char head, the same `(quoteStringLit-chars name
-- ++ inner) ++ outer-suffix` shape works after the `' ' ∷` folds in.
build-EmitsOK-stdScopeFmt :
  ∀ (s : RawStdScope) (name inner outer-suffix : List Char)
  → EmitsOK stdScopeFmt s
      ((quoteStringLit-chars name ++ₗ inner) ++ₗ outer-suffix)
build-EmitsOK-stdScopeFmt RssNode _ _ _ = tt , ∷-stop refl
build-EmitsOK-stdScopeFmt RssMsg _ _ _ =
  (tt , ∷-stop refl) , (λ _ → refl)
build-EmitsOK-stdScopeFmt RssSig _ _ _ =
  (tt , ∷-stop refl) , (λ _ → refl)
build-EmitsOK-stdScopeFmt RssEnv _ _ _ =
  (tt , ∷-stop refl) , (λ _ → refl)
build-EmitsOK-stdScopeFmt RssNet _ _ _ = tt , (λ _ → refl)

-- Relation scope: at `attrDefRelFmt`'s call site the suffix is
-- `' ' ∷ (quoteStringLit-chars name ++ inner) ++ outer-suffix` (leading
-- ' ' from the explicit `withWS` between `relScopeFmt` and `stringLit`).
-- BU_BO_REL_ / BU_SG_REL_ both START with 'B' so their inner SuffixStops
-- on the trailing-suffix close by `∷-stop refl` on '"' (after the leading
-- ' ' from withWS and the BU_BO_REL_ keyword folds through).  Wait —
-- actually, we don't need any SuffixStops witness for `withPrefix
-- "BU_BO_REL_" ws` because `relScopeFmt` is `altSum (literal …) (literal
-- …)` (NO inner ws).  So this is much simpler than std scope.
build-EmitsOK-relScopeFmt :
  ∀ (s : RawRelScope) (suffix : List Char)
  → EmitsOK relScopeFmt s suffix
build-EmitsOK-relScopeFmt RrsNodeMsg _ = tt
build-EmitsOK-relScopeFmt RrsNodeSig _ = tt , (λ _ → refl)

-- Attribute type: suffix shape `' ' ∷ rest` (head `' '` is hspace, but
-- not a digit and not `.`).  Inner slots use the `showXxx-chars-head-stop`
-- helpers to bridge the `showInt-chars zmn ++ ...` shapes back to
-- `SuffixStops isHSpace`.
build-EmitsOK-attrTypeFmt :
  ∀ (rt : RawAttrType) (rest : List Char)
  → EmitsOK attrTypeFmt rt (' ' ∷ rest)
build-EmitsOK-attrTypeFmt RatString rest = tt
build-EmitsOK-attrTypeFmt (RatInt mn mx) rest =
    inner , (λ _ → refl)
  where
    zmn = intDecRatToℤ mn
    zmx = intDecRatToℤ mx
    -- Innermost: `intDecRat mx` with suffix `' ' ∷ rest`.  Both witnesses
    -- close: head `' '` is non-digit; `'.' ≢ ' '`.
    mx-emits : EmitsOK intDecRat mx (' ' ∷ rest)
    mx-emits = ∷-stop refl , (λ ())
    -- Leading ws of `withWS intDecRat` (between mn and mx) requires
    -- `SuffixStops isHSpace (showInt-chars zmx ++ ' ' ∷ rest)` — head
    -- of `showInt-chars zmx` is non-hspace.
    ws-mid : SuffixStops isHSpace (showInt-chars zmx ++ₗ (' ' ∷ rest))
    ws-mid = showInt-chars-head-stop zmx (' ' ∷ rest)
    mx-withws : EmitsOK (withWS intDecRat) mx (' ' ∷ rest)
    mx-withws = ws-mid , mx-emits
    -- intDecRat mn with suffix `(' ' ∷ showInt-chars zmx) ++ ' ' ∷ rest`
    -- which reduces (by `(c ∷ xs) ++ ys = c ∷ (xs ++ ys)`) to
    -- `' ' ∷ (showInt-chars zmx ++ ' ' ∷ rest)` — head `' '`, both
    -- witnesses close as for mx-emits.
    mn-emits : EmitsOK intDecRat mn ((' ' ∷ showInt-chars zmx) ++ₗ (' ' ∷ rest))
    mn-emits = ∷-stop refl , (λ ())
    pair-emits : EmitsOK (pair intDecRat (withWS intDecRat))
                          (mn , mx) (' ' ∷ rest)
    pair-emits = mn-emits , mx-withws
    -- Leading ws of `withWS (pair intDecRat (withWS intDecRat))` after
    -- `INT`: suffix `(showInt-chars zmn ++ (' ' ∷ showInt-chars zmx))
    -- ++ ' ' ∷ rest` (left-associated; ++-assoc bridges to right form).
    ws-leading : SuffixStops isHSpace
      ((showInt-chars zmn ++ₗ (' ' ∷ showInt-chars zmx)) ++ₗ (' ' ∷ rest))
    ws-leading = assoc-bridgeᴴ (showInt-chars zmn) _ _
                   (showInt-chars-head-stop zmn _)
    body-emits : EmitsOK (withWS (pair intDecRat (withWS intDecRat)))
                          (mn , mx) (' ' ∷ rest)
    body-emits = ws-leading , pair-emits
    inner : EmitsOK intArm (mn , mx) (' ' ∷ rest)
    inner = tt , body-emits
build-EmitsOK-attrTypeFmt (RatFloat mn mx) rest =
    (inner , (λ _ → refl)) , (λ _ → refl)
  where
    mx-emits : EmitsOK decRat mx (' ' ∷ rest)
    mx-emits = ∷-stop refl
    ws-mid : SuffixStops isHSpace (showDecRat-dec-chars mx ++ₗ (' ' ∷ rest))
    ws-mid = showDecRat-chars-head-stop mx (' ' ∷ rest)
    mx-withws : EmitsOK (withWS decRat) mx (' ' ∷ rest)
    mx-withws = ws-mid , mx-emits
    mn-emits : EmitsOK decRat mn
                 ((' ' ∷ showDecRat-dec-chars mx) ++ₗ (' ' ∷ rest))
    mn-emits = ∷-stop refl
    pair-emits : EmitsOK (pair decRat (withWS decRat))
                          (mn , mx) (' ' ∷ rest)
    pair-emits = mn-emits , mx-withws
    ws-leading : SuffixStops isHSpace
      ((showDecRat-dec-chars mn ++ₗ (' ' ∷ showDecRat-dec-chars mx)) ++ₗ
       (' ' ∷ rest))
    ws-leading = assoc-bridgeᴴ (showDecRat-dec-chars mn) _ _
                   (showDecRat-chars-head-stop mn _)
    body-emits : EmitsOK (withWS (pair decRat (withWS decRat)))
                          (mn , mx) (' ' ∷ rest)
    body-emits = ws-leading , pair-emits
    inner : EmitsOK floatArm (mn , mx) (' ' ∷ rest)
    inner = tt , body-emits
build-EmitsOK-attrTypeFmt (RatEnum h t) rest =
    ((enumArm-OK , (λ _ → refl)) , (λ _ → refl)) , (λ _ → refl)
  where
    -- The trailing element-fail witness for the empty case of `many`:
    -- after exhausting all tail labels, the next char is `' '` (the
    -- canonical separator before `;`).  parseCharsSeq "," on `' ' ∷ …`
    -- fails on `',' ≈ᵇ ' '` by closed-Char reduction.
    fails-at-rest :
      ParseFailsAt (withPrefix (',' ∷ []) (withWSOpt stringLit)) (' ' ∷ rest)
    fails-at-rest _ = refl

    -- Per-element EmitsOK for one tail label `x` with the remaining-tail
    -- emit prepended to outer-suffix `' ' ∷ rest`.  The `withPrefix ","
    -- (withWSOpt stringLit)` reduces to:
    --   tt (literal ",")
    --   × SuffixStops isHSpace (quoteStringLit-chars x ++ ...)
    --   × tt (wsOpt iso strip)
    --   × SuffixStops `_≈ᵇ '"'` (quote-stop on the trailing-list emit)
    elem-OK : ∀ (x : List Char) (xs : List (List Char))
      → SuffixStops (λ c → c ≈ᵇ '"')
          (Data.List.concatMap
            (λ y → ',' ∷ quoteStringLit-chars y) xs ++ₗ (' ' ∷ rest))
      → EmitsOK (withPrefix (',' ∷ []) (withWSOpt stringLit)) x
          (Data.List.concatMap
            (λ y → ',' ∷ quoteStringLit-chars y) xs ++ₗ (' ' ∷ rest))
    elem-OK x xs stops-quote =
      tt , (∷-stop refl , stops-quote)

    -- Quote-stop witness: head of `concatMap (...) xs ++ ' ' ∷ rest`
    -- is either `,` (xs non-empty) or `' '` (xs empty); both non-`"`.
    rest-stops-quote : ∀ (xs : List (List Char))
      → SuffixStops (λ c → c ≈ᵇ '"')
          (Data.List.concatMap
            (λ y → ',' ∷ quoteStringLit-chars y) xs ++ₗ (' ' ∷ rest))
    rest-stops-quote []      = ∷-stop refl
    rest-stops-quote (_ ∷ _) = ∷-stop refl

    -- EmitsOKMany over the tail label list.  Each non-empty cell's emit
    -- starts with `,` (length ≥ 1).
    build-many : ∀ (xs : List (List Char))
      → EmitsOK (many (withPrefix (',' ∷ []) (withWSOpt stringLit))) xs
          (' ' ∷ rest)
    build-many []       =
      Aletheia.DBC.TextParser.Format.EmitsOKMany.[]-fails fails-at-rest
    build-many (x ∷ xs) =
      Aletheia.DBC.TextParser.Format.EmitsOKMany.∷-cons
        (elem-OK x xs (rest-stops-quote xs))
        (Data.Nat.s≤s Data.Nat.z≤n)
        (build-many xs)

    enumBody-OK :
      EmitsOK (pair stringLit
                (many (withPrefix (',' ∷ []) (withWSOpt stringLit))))
              (h , t) (' ' ∷ rest)
    enumBody-OK = rest-stops-quote t , build-many t

    -- The `withWS` after "ENUM" needs `SuffixStops isHSpace` on the
    -- emit-of-pair `quoteStringLit-chars h ++ concatMap (...) t ++ ' ' ∷ rest`.
    -- Head is `'"'` definitionally (`quoteStringLit-chars` always starts
    -- with `'"'`), non-hspace.
    enum-leading-ws :
      SuffixStops isHSpace
        (emit (pair stringLit
                 (many (withPrefix (',' ∷ []) (withWSOpt stringLit))))
              (h , t)
         ++ₗ (' ' ∷ rest))
    enum-leading-ws = ∷-stop refl

    enumArm-OK : EmitsOK enumArm (h , t) (' ' ∷ rest)
    enumArm-OK = tt , (enum-leading-ws , enumBody-OK)
build-EmitsOK-attrTypeFmt (RatHex mn mx) rest =
    (((inner , (λ _ → refl)) , (λ _ → refl)) , (λ _ → refl)) , (λ _ → refl)
  where
    nmn = natDecRatToℕ mn
    nmx = natDecRatToℕ mx
    mx-emits : EmitsOK natDecRat mx (' ' ∷ rest)
    mx-emits = ∷-stop refl , (λ ())
    ws-mid : SuffixStops isHSpace (showNat-chars nmx ++ₗ (' ' ∷ rest))
    ws-mid = showNat-chars-head-stop nmx (' ' ∷ rest)
    mx-withws : EmitsOK (withWS natDecRat) mx (' ' ∷ rest)
    mx-withws = ws-mid , mx-emits
    mn-emits : EmitsOK natDecRat mn
                 ((' ' ∷ showNat-chars nmx) ++ₗ (' ' ∷ rest))
    mn-emits = ∷-stop refl , (λ ())
    pair-emits : EmitsOK (pair natDecRat (withWS natDecRat))
                          (mn , mx) (' ' ∷ rest)
    pair-emits = mn-emits , mx-withws
    ws-leading : SuffixStops isHSpace
      ((showNat-chars nmn ++ₗ (' ' ∷ showNat-chars nmx)) ++ₗ (' ' ∷ rest))
    ws-leading = assoc-bridgeᴴ (showNat-chars nmn) _ _
                   (showNat-chars-head-stop nmn _)
    body-emits : EmitsOK (withWS (pair natDecRat (withWS natDecRat)))
                          (mn , mx) (' ' ∷ rest)
    body-emits = ws-leading , pair-emits
    inner : EmitsOK hexArm (mn , mx) (' ' ∷ rest)
    inner = tt , body-emits

-- ============================================================================
-- TOP-LEVEL BUILDERS — full attrDefFmt / attrDefRelFmt EmitsOK
-- ============================================================================

private
  -- Head-non-hspace dispatch on `RawAttrType`: `emit attrTypeFmt rt`
  -- starts with `'S'` / `'I'` / `'F'` / `'E'` / `'H'` per case (the
  -- keyword's first char), all non-hspace.  Bridge through `++` left-
  -- association for the call-site shape `(emit attrTypeFmt rt ++ mid)
  -- ++ rest`.
  attrType-emit-leading-non-hspace :
    ∀ (rt : RawAttrType) (mid rest : List Char)
    → SuffixStops isHSpace ((emit attrTypeFmt rt ++ₗ mid) ++ₗ rest)
  attrType-emit-leading-non-hspace RatString _ _ = ∷-stop refl
  attrType-emit-leading-non-hspace (RatInt _ _) _ _ = ∷-stop refl
  attrType-emit-leading-non-hspace (RatFloat _ _) _ _ = ∷-stop refl
  attrType-emit-leading-non-hspace (RatEnum _ _) _ _ = ∷-stop refl
  attrType-emit-leading-non-hspace (RatHex _ _) _ _ = ∷-stop refl

  -- Head-non-hspace dispatch on `RawStdScope` for the leading-ws slot
  -- of `attrDefFmt`.  The suffix is `(emit stdScopeFmt s ++ inner) ++
  -- outer-suffix`; per scope, the head reduces to a closed Char (`'B'`
  -- / `'S'` / `'E'` for keyword scopes; `'"'` for `RssNet`'s empty emit
  -- followed by quoteStringLit-chars).
  stdScope-emit-leading-non-hspace :
    ∀ (s : RawStdScope) (n : List Char) (inner outer-suffix : List Char)
    → SuffixStops isHSpace
        ((emit stdScopeFmt s ++ₗ (quoteStringLit-chars n ++ₗ inner)) ++ₗ
         outer-suffix)
  stdScope-emit-leading-non-hspace RssNet  _ _ _ = ∷-stop refl
  stdScope-emit-leading-non-hspace RssNode _ _ _ = ∷-stop refl
  stdScope-emit-leading-non-hspace RssMsg  _ _ _ = ∷-stop refl
  stdScope-emit-leading-non-hspace RssSig  _ _ _ = ∷-stop refl
  stdScope-emit-leading-non-hspace RssEnv  _ _ _ = ∷-stop refl

  -- Head-non-hspace dispatch on `RawRelScope`.  Both keywords start
  -- with `'B'`.
  relScope-emit-leading-non-hspace :
    ∀ (s : RawRelScope) (mid rest : List Char)
    → SuffixStops isHSpace ((emit relScopeFmt s ++ₗ mid) ++ₗ rest)
  relScope-emit-leading-non-hspace RrsNodeMsg _ _ = ∷-stop refl
  relScope-emit-leading-non-hspace RrsNodeSig _ _ = ∷-stop refl

-- Top-level builder for `attrDefFmt`: assembles the 10-element EmitsOK
-- tuple by combining the per-Format sub-builders + per-case head-stop
-- helpers.  `outer-suffix` and all four record fields are universal.
build-EmitsOK-attrDefFmt :
  ∀ (s : RawStdScope) (n : List Char) (rt : RawAttrType) (outer-suffix : List Char)
  → EmitsOK attrDefFmt (s , n , rt , tt) outer-suffix
build-EmitsOK-attrDefFmt s n rt outer-suffix =
  -- L1: literal "BA_DEF_" — vacuous.
    tt
  -- L2: leading withWS after "BA_DEF_": SuffixStops isHSpace on
  --     `(emit stdScopeFmt s ++ (quoteStringLit-chars n ++ ' ' ∷ ...))
  --     ++ outer-suffix`.  Per-scope head-stop closes by ∷-stop refl.
  , stdScope-emit-leading-non-hspace s n inner-after-name outer-suffix
  -- L3: stdScopeFmt EmitsOK — sub-builder, concrete-shape `(quoteStringLit
  --     ++ inner) ++ outer-suffix`.
  , build-EmitsOK-stdScopeFmt s n inner-after-name outer-suffix
  -- L4: stringLit SuffixStops `_≈ᵇ '"'` on suffix `' ' ∷ ...`.  ∷-stop refl.
  , ∷-stop refl
  -- L5: leading withWS after name: SuffixStops isHSpace on `(emit attrTypeFmt
  --     rt ++ ' ' ∷ ';' ∷ '\n' ∷ []) ++ outer-suffix`.  Per-rt head-stop.
  , attrType-emit-leading-non-hspace rt
      (' ' ∷ ';' ∷ '\n' ∷ []) outer-suffix
  -- L6: attrTypeFmt EmitsOK — sub-builder, suffix `' ' ∷ ';' ∷ '\n' ∷ os`.
  , build-EmitsOK-attrTypeFmt rt (';' ∷ '\n' ∷ outer-suffix)
  -- L7: leading withWSCanonOne: SuffixStops isHSpace on `';' ∷ '\n' ∷ os`.
  , ∷-stop refl
  -- L8: literal ";" — vacuous.
  , tt
  -- L9: newlineFmt iso reduction — literal "\n" vacuous.
  , tt
  -- L10: newlineFmt altSum disjointness — parse "\r\n" on `'\n' ∷ os`
  --      fails on first-char comparison.  λ _ → refl.
  , λ _ → refl
  where
    -- inner = emit (pair stringLit (withWS (pair attrTypeFmt (...)))) (n, rt, tt)
    -- minus the `quoteStringLit-chars n` prefix (which is supplied
    -- explicitly to `build-EmitsOK-stdScopeFmt`).
    inner-after-name : List Char
    inner-after-name = ' ' ∷ (emit attrTypeFmt rt ++ₗ ' ' ∷ ';' ∷ '\n' ∷ [])

-- Top-level builder for `attrDefRelFmt`: same structure with rel scope
-- and an explicit `withWS` between scope and name (instead of the std
-- case's withPrefix-internalised trailing space).  11 elements total
-- (one extra leading-ws slot vs std).
build-EmitsOK-attrDefRelFmt :
  ∀ (s : RawRelScope) (n : List Char) (rt : RawAttrType) (outer-suffix : List Char)
  → EmitsOK attrDefRelFmt (s , n , rt , tt) outer-suffix
build-EmitsOK-attrDefRelFmt s n rt outer-suffix =
  -- L1: literal "BA_DEF_REL_" — vacuous.
    tt
  -- L2: leading withWS after "BA_DEF_REL_": SuffixStops on
  --     `(emit relScopeFmt s ++ ' ' ∷ ...) ++ outer-suffix`.
  , relScope-emit-leading-non-hspace s
      (' ' ∷ (quoteStringLit-chars n ++ₗ inner-after-name)) outer-suffix
  -- L3: relScopeFmt EmitsOK — sub-builder.
  , build-EmitsOK-relScopeFmt s _
  -- L4: leading withWS after rel scope: SuffixStops on
  --     `(quoteStringLit-chars n ++ ' ' ∷ emit attrTypeFmt rt ++ ...) ++ outer-suffix`.
  --     Head '"' from quoteStringLit-chars folds.  ∷-stop refl.
  , ∷-stop refl
  -- L5: stringLit SuffixStops `_≈ᵇ '"'` on `' ' ∷ ...`.  ∷-stop refl.
  , ∷-stop refl
  -- L6: leading withWS after name: SuffixStops on attrTypeFmt emit head.
  , attrType-emit-leading-non-hspace rt
      (' ' ∷ ';' ∷ '\n' ∷ []) outer-suffix
  -- L7: attrTypeFmt EmitsOK.
  , build-EmitsOK-attrTypeFmt rt (';' ∷ '\n' ∷ outer-suffix)
  -- L8: leading withWSCanonOne.
  , ∷-stop refl
  -- L9: literal ";".
  , tt
  -- L10: newlineFmt literal "\n" inj₂ inner.
  , tt
  -- L11: newlineFmt altSum disjointness.
  , λ _ → refl
  where
    inner-after-name : List Char
    inner-after-name = ' ' ∷ (emit attrTypeFmt rt ++ₗ ' ' ∷ ';' ∷ '\n' ∷ [])

-- ============================================================================
-- UNIVERSAL ROUNDTRIPS — one-liner via Format DSL `roundtrip`
-- ============================================================================

-- ∀ pos, scope, name, type, outer-suffix:
--   parse attrDefFmt pos (emit attrDefFmt (s, n, rt, tt) ++ outer-suffix)
--   ≡ just (mkResult (s, n, rt, tt) ...).
-- Single `roundtrip attrDefFmt` call backed by the EmitsOK builder.
parseAttrDef-format-roundtrip :
  ∀ (pos : Position) (s : RawStdScope) (n : List Char) (rt : RawAttrType)
    (outer-suffix : List Char)
  → parse attrDefFmt pos
      (emit attrDefFmt (s , n , rt , tt) ++ₗ outer-suffix)
    ≡ just (mkResult (s , n , rt , tt)
              (advancePositions pos
                (emit attrDefFmt (s , n , rt , tt)))
              outer-suffix)
parseAttrDef-format-roundtrip pos s n rt outer-suffix =
  roundtrip attrDefFmt pos (s , n , rt , tt) outer-suffix
            (build-EmitsOK-attrDefFmt s n rt outer-suffix)

-- Mirror for BA_DEF_REL_.
parseAttrDefRel-format-roundtrip :
  ∀ (pos : Position) (s : RawRelScope) (n : List Char) (rt : RawAttrType)
    (outer-suffix : List Char)
  → parse attrDefRelFmt pos
      (emit attrDefRelFmt (s , n , rt , tt) ++ₗ outer-suffix)
    ≡ just (mkResult (s , n , rt , tt)
              (advancePositions pos
                (emit attrDefRelFmt (s , n , rt , tt)))
              outer-suffix)
parseAttrDefRel-format-roundtrip pos s n rt outer-suffix =
  roundtrip attrDefRelFmt pos (s , n , rt , tt) outer-suffix
            (build-EmitsOK-attrDefRelFmt s n rt outer-suffix)
