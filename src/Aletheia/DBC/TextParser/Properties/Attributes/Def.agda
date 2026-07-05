-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.5.d 3c-A — slim `parseAttrDef-roundtrip` /
-- `parseAttrDefRel-roundtrip` derived from the universal Format DSL
-- roundtrip (`Format.AttrDef`).
--
-- Pre-3d.5.d (3c.1): hand-written 1,428-line bind-chain proofs through
-- 14 parser primitives per scope (`parseAttrDef-roundtrip` × 5 std-scope
-- cases + `parseAttrDefRel-roundtrip` × 2 rel-scope cases) + 5-way
-- attribute-type dispatcher.
--
-- Post-3d.5.d: per-scope wrappers around the universal `parseAttrDef-
-- format-roundtrip` / `parseAttrDefRel-format-roundtrip` lemmas, plus
-- two per-construct bridges (`emit attrDefFmt raw ≡ emitAttrDef-chars
-- d` per std scope; same for rel) and the η-style trailing-newline /
-- pure-lift composition.
module Aletheia.DBC.TextParser.Properties.Attributes.Def where

open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; length) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (just)
open import Data.Product using (_,_; proj₂)
open import Data.String using ()
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst₂)

open import Aletheia.Parser.Combinators
  using (Position; Parser; mkResult; advancePositions;
         _>>=_; pure; many)
open import Aletheia.DBC.Types using
  ( AttrType; ATInt; ATFloat; ATString; ATEnum; ATHex
  ; ASNetwork; ASNode; ASMessage; ASSignal; ASEnvVar
  ; ASNodeMsg; ASNodeSig
  ; AttrDef; mkAttrDef)

open import Aletheia.DBC.TextParser.Attributes using
  (parseAttrDef; parseAttrDefRel)
open import Aletheia.DBC.TextParser.Lexer using (parseNewline)
open import Aletheia.DBC.TextFormatter.Attributes using
  (emitAttrDef-chars; emitAttrType-chars)
open import Aletheia.DBC.TextFormatter.Emitter using (quoteStringLit-chars)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; bind-just-step)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart; manyHelper-parseNewline-exhaust)

open import Aletheia.DBC.TextParser.Format using
  (emit; parse)
open import Aletheia.DBC.TextParser.Format.AttrDef as FmtAD using
  ( RawStdScope; RssNet; RssNode; RssMsg; RssSig; RssEnv
  ; RawRelScope; RrsNodeMsg; RrsNodeSig
  ; RawAttrType; RatString; RatInt; RatFloat; RatEnum; RatHex
  ; liftStdScope; liftRelScope; liftAttrType
  ; liftStdAttrDef; liftRelAttrDef
  ; attrDefFmt; attrDefRelFmt; attrTypeFmt
  ; parseAttrDef-format-roundtrip
  ; parseAttrDefRel-format-roundtrip)

-- ============================================================================
-- WELL-FORMEDNESS PREDICATES — kept for source compatibility with the
-- `Properties/Attributes` facade and downstream Layer-4 callers
-- (`Properties/Attributes/Line.agda`).
-- ============================================================================

-- WfAttrType: ENUM must be non-empty (DBC grammar requirement; an empty
-- ENUM is rejected at the lexical level by `parseEnumLabels`'s `do
-- h ← parseStringLit; t ← many ...; pure (h ∷ t)` — at least one label).
data WfAttrType : AttrType → Set where
  WfATInt    : ∀ mn mx → WfAttrType (ATInt mn mx)
  WfATFloat  : ∀ mn mx → WfAttrType (ATFloat mn mx)
  WfATString : WfAttrType ATString
  WfATEnum   : ∀ x xs → WfAttrType (ATEnum (x ∷ xs))
  WfATHex    : ∀ mn mx → WfAttrType (ATHex mn mx)

-- WfAttrDef-NotRel: scope is a standard scope (not rel).  Carries
-- `WfAttrType` for the type field.
data WfAttrDef-NotRel : AttrDef → Set where
  Wf-Network : ∀ {n ty} → WfAttrType ty → WfAttrDef-NotRel (mkAttrDef n ASNetwork ty)
  Wf-Node    : ∀ {n ty} → WfAttrType ty → WfAttrDef-NotRel (mkAttrDef n ASNode    ty)
  Wf-Message : ∀ {n ty} → WfAttrType ty → WfAttrDef-NotRel (mkAttrDef n ASMessage ty)
  Wf-Signal  : ∀ {n ty} → WfAttrType ty → WfAttrDef-NotRel (mkAttrDef n ASSignal  ty)
  Wf-EnvVar  : ∀ {n ty} → WfAttrType ty → WfAttrDef-NotRel (mkAttrDef n ASEnvVar  ty)

-- WfAttrDef-Rel: scope is a rel scope.
data WfAttrDef-Rel : AttrDef → Set where
  Wf-NodeMsg : ∀ {n ty} → WfAttrType ty → WfAttrDef-Rel (mkAttrDef n ASNodeMsg ty)
  Wf-NodeSig : ∀ {n ty} → WfAttrType ty → WfAttrDef-Rel (mkAttrDef n ASNodeSig ty)

-- ============================================================================
-- WfAttrType → RawAttrType
-- ============================================================================

-- Total inverse of `liftAttrType` for well-formed AttrType values.
rawAttrTypeOf : ∀ {ty : AttrType} → WfAttrType ty → RawAttrType
rawAttrTypeOf (WfATInt mn mx)   = RatInt mn mx
rawAttrTypeOf (WfATFloat mn mx) = RatFloat mn mx
rawAttrTypeOf  WfATString       = RatString
rawAttrTypeOf (WfATEnum x xs)   = RatEnum x xs
rawAttrTypeOf (WfATHex mn mx)   = RatHex mn mx

-- `liftAttrType (rawAttrTypeOf wf)` recovers the original `ty`.  Per
-- WfAttrType case, all 5 reduce by `refl`.
liftAttrType-rawAttrTypeOf : ∀ {ty : AttrType} (wf : WfAttrType ty)
  → liftAttrType (rawAttrTypeOf wf) ≡ ty
liftAttrType-rawAttrTypeOf (WfATInt _ _)   = refl
liftAttrType-rawAttrTypeOf (WfATFloat _ _) = refl
liftAttrType-rawAttrTypeOf  WfATString     = refl
liftAttrType-rawAttrTypeOf (WfATEnum _ _)  = refl
liftAttrType-rawAttrTypeOf (WfATHex _ _)   = refl

-- ============================================================================
-- BRIDGES: emit Format-DSL ≡ existing emit*-chars
-- ============================================================================

-- ENUM-specific helper: `concatMap (λ y → ',' ∷ quoteStringLit-chars y)`
-- is propositionally — but not definitionally — equal to the formatter's
-- `foldr (λ y acc → ',' ∷ quoteStringLit-chars y ++ acc) []` (stdlib's
-- `concatMap = concat ∘ map`, while the formatter inlines a foldr).
-- Bridge by structural induction.
private
  open import Data.List using (concatMap; foldr)

  concatMap-foldr-bridge : ∀ (xs : List (List Char))
    → concatMap (λ y → ',' ∷ quoteStringLit-chars y) xs
      ≡ foldr (λ y acc → ',' ∷ quoteStringLit-chars y ++ₗ acc) [] xs
  concatMap-foldr-bridge []       = refl
  concatMap-foldr-bridge (x ∷ xs) =
    cong (λ z → ',' ∷ (quoteStringLit-chars x ++ₗ z))
         (concatMap-foldr-bridge xs)

-- DSL emit ≡ formatter emit for each `RawAttrType` case.  4 of 5 close
-- by `refl` (the iso/altSum reductions yield the same flat character
-- sequence modulo `_++_` definitional equalities).  RatEnum needs the
-- `concatMap-foldr-bridge` for the tail label list.
emit-attrTypeFmt-eq-emitAttrType-chars :
  ∀ (rt : RawAttrType)
  → emit attrTypeFmt rt ≡ emitAttrType-chars (liftAttrType rt)
emit-attrTypeFmt-eq-emitAttrType-chars RatString       = refl
emit-attrTypeFmt-eq-emitAttrType-chars (RatInt _ _)    = refl
emit-attrTypeFmt-eq-emitAttrType-chars (RatFloat _ _)  = refl
emit-attrTypeFmt-eq-emitAttrType-chars (RatEnum h t)   =
  cong (λ z → 'E' ∷ 'N' ∷ 'U' ∷ 'M' ∷ ' ' ∷ (quoteStringLit-chars h ++ₗ z))
       (concatMap-foldr-bridge t)
emit-attrTypeFmt-eq-emitAttrType-chars (RatHex _ _)    = refl

-- DSL emit ≡ formatter emit for the full BA_DEF_ line.  Per std scope
-- (5 cases), both sides reduce to the same `<closed BA_DEF_ + scope
-- bytes> ++ qsl n ++ ' ' ∷ <attrType bytes> ++ ' ' ∷ ';' ∷ '\n' ∷ []`
-- shape, with `<attrType bytes>` differing only between LHS (`emit
-- attrTypeFmt rt`) and RHS (`emitAttrType-chars (liftAttrType rt)`).
-- Bridge by `cong` over `emit-attrTypeFmt-eq-emitAttrType-chars`.
emit-attrDefFmt-eq-emitAttrDef-chars :
  ∀ (s : RawStdScope) (n : List Char) (rt : RawAttrType)
  → emit attrDefFmt (s , n , rt , tt)
    ≡ emitAttrDef-chars (mkAttrDef n (liftStdScope s) (liftAttrType rt))
emit-attrDefFmt-eq-emitAttrDef-chars RssNet n rt =
  cong (λ z → 'B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ ' ' ∷
              (quoteStringLit-chars n ++ₗ
               ' ' ∷ (z ++ₗ ' ' ∷ ';' ∷ '\n' ∷ [])))
       (emit-attrTypeFmt-eq-emitAttrType-chars rt)
emit-attrDefFmt-eq-emitAttrDef-chars RssNode n rt =
  cong (λ z → 'B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ ' ' ∷
              'B' ∷ 'U' ∷ '_' ∷ ' ' ∷
              (quoteStringLit-chars n ++ₗ
               ' ' ∷ (z ++ₗ ' ' ∷ ';' ∷ '\n' ∷ [])))
       (emit-attrTypeFmt-eq-emitAttrType-chars rt)
emit-attrDefFmt-eq-emitAttrDef-chars RssMsg n rt =
  cong (λ z → 'B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ ' ' ∷
              'B' ∷ 'O' ∷ '_' ∷ ' ' ∷
              (quoteStringLit-chars n ++ₗ
               ' ' ∷ (z ++ₗ ' ' ∷ ';' ∷ '\n' ∷ [])))
       (emit-attrTypeFmt-eq-emitAttrType-chars rt)
emit-attrDefFmt-eq-emitAttrDef-chars RssSig n rt =
  cong (λ z → 'B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ ' ' ∷
              'S' ∷ 'G' ∷ '_' ∷ ' ' ∷
              (quoteStringLit-chars n ++ₗ
               ' ' ∷ (z ++ₗ ' ' ∷ ';' ∷ '\n' ∷ [])))
       (emit-attrTypeFmt-eq-emitAttrType-chars rt)
emit-attrDefFmt-eq-emitAttrDef-chars RssEnv n rt =
  cong (λ z → 'B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ ' ' ∷
              'E' ∷ 'V' ∷ '_' ∷ ' ' ∷
              (quoteStringLit-chars n ++ₗ
               ' ' ∷ (z ++ₗ ' ' ∷ ';' ∷ '\n' ∷ [])))
       (emit-attrTypeFmt-eq-emitAttrType-chars rt)

-- DSL emit ≡ formatter emit for the full BA_DEF_REL_ line.  Per rel
-- scope (2 cases).
emit-attrDefRelFmt-eq-emitAttrDef-chars :
  ∀ (s : RawRelScope) (n : List Char) (rt : RawAttrType)
  → emit attrDefRelFmt (s , n , rt , tt)
    ≡ emitAttrDef-chars (mkAttrDef n (liftRelScope s) (liftAttrType rt))
emit-attrDefRelFmt-eq-emitAttrDef-chars RrsNodeMsg n rt =
  cong (λ z → 'B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷
              'R' ∷ 'E' ∷ 'L' ∷ '_' ∷ ' ' ∷
              'B' ∷ 'U' ∷ '_' ∷ 'B' ∷ 'O' ∷ '_' ∷
              'R' ∷ 'E' ∷ 'L' ∷ '_' ∷ ' ' ∷
              (quoteStringLit-chars n ++ₗ
               ' ' ∷ (z ++ₗ ' ' ∷ ';' ∷ '\n' ∷ [])))
       (emit-attrTypeFmt-eq-emitAttrType-chars rt)
emit-attrDefRelFmt-eq-emitAttrDef-chars RrsNodeSig n rt =
  cong (λ z → 'B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷
              'R' ∷ 'E' ∷ 'L' ∷ '_' ∷ ' ' ∷
              'B' ∷ 'U' ∷ '_' ∷ 'S' ∷ 'G' ∷ '_' ∷
              'R' ∷ 'E' ∷ 'L' ∷ '_' ∷ ' ' ∷
              (quoteStringLit-chars n ++ₗ
               ' ' ∷ (z ++ₗ ' ' ∷ ';' ∷ '\n' ∷ [])))
       (emit-attrTypeFmt-eq-emitAttrType-chars rt)

-- ============================================================================
-- SLIM `parseAttrDef-roundtrip` — std scope (`isRelScope ≡ false`) variant
-- ============================================================================

-- Per-scope helper: given a raw carrier `(s, n, rt, tt)`, the wrapped
-- parser succeeds and returns the lifted AttrDef.
private
  parseAttrDef-roundtrip-raw :
      ∀ (pos : Position) (s : RawStdScope) (n : List Char) (rt : RawAttrType)
        (outer-suffix : List Char)
    → SuffixStops isNewlineStart outer-suffix
    → proj₂ (parseAttrDef pos
        (emitAttrDef-chars (mkAttrDef n (liftStdScope s) (liftAttrType rt))
         ++ₗ outer-suffix))
      ≡ just (mkResult (mkAttrDef n (liftStdScope s) (liftAttrType rt))
               (advancePositions pos
                 (emitAttrDef-chars
                   (mkAttrDef n (liftStdScope s) (liftAttrType rt))))
               outer-suffix)
  parseAttrDef-roundtrip-raw pos s n rt outer-suffix nl-stop =
    trans (cong (λ inp → proj₂ (parseAttrDef pos (inp ++ₗ outer-suffix)))
                (sym bridge))
      (trans step-format
        (trans step-many-newline step-pure))
    where
      d : AttrDef
      d = mkAttrDef n (liftStdScope s) (liftAttrType rt)

      bridge : emit attrDefFmt (s , n , rt , tt) ≡ emitAttrDef-chars d
      bridge = emit-attrDefFmt-eq-emitAttrDef-chars s n rt

      pos-line : Position
      pos-line = advancePositions pos (emit attrDefFmt (s , n , rt , tt))

      cont-line : FmtAD.StdAttrDefCarrier → Parser AttrDef
      cont-line c = many parseNewline >>= λ _ → pure (liftStdAttrDef c)

      cont-blanks : List Char → Parser AttrDef
      cont-blanks _ = pure (liftStdAttrDef (s , n , rt , tt))

      -- Step 1: parse attrDefFmt succeeds via the universal roundtrip.
      step-format :
        proj₂ (parseAttrDef pos
                (emit attrDefFmt (s , n , rt , tt) ++ₗ outer-suffix))
        ≡ proj₂ (cont-line (s , n , rt , tt) pos-line outer-suffix)
      step-format =
        bind-just-step (parse attrDefFmt) cont-line
                       pos (emit attrDefFmt (s , n , rt , tt) ++ₗ outer-suffix)
                       (s , n , rt , tt) pos-line outer-suffix
                       (parseAttrDef-format-roundtrip pos s n rt outer-suffix)

      -- Step 2: many parseNewline consumes zero from outer-suffix.
      step-many-newline :
        proj₂ (cont-line (s , n , rt , tt) pos-line outer-suffix)
        ≡ proj₂ (cont-blanks [] pos-line outer-suffix)
      step-many-newline =
        bind-just-step (many parseNewline) cont-blanks
                       pos-line outer-suffix
                       [] pos-line outer-suffix
                       (manyHelper-parseNewline-exhaust
                         pos-line outer-suffix (length outer-suffix) nl-stop)

      -- Step 3: pure (liftStdAttrDef (s, n, rt, tt)) returns; convert
      -- pos-line back to `advancePositions pos (emitAttrDef-chars d)`
      -- via the bridge, and `liftStdAttrDef (s, n, rt, tt) = d`
      -- (definitional — the AttrDef record's three fields are exactly
      -- the lifted values).
      step-pure :
        proj₂ (cont-blanks [] pos-line outer-suffix)
        ≡ just (mkResult d
                 (advancePositions pos (emitAttrDef-chars d))
                 outer-suffix)
      step-pure =
        cong (λ p → just (mkResult d p outer-suffix))
             (cong (advancePositions pos) bridge)

-- Top-level: pattern-match on `WfAttrDef-NotRel` to recover (s, rt),
-- then transport the raw helper along the scope and attr-type
-- equalities.  `subst₂` (rather than `subst` over the attr-type alone)
-- keeps the raw instance's `liftStdScope s` scope form intact, so the
-- conversion checker matches the motive instance syntactically and
-- never unfolds `parseAttrDef` on the concrete-scope input (which
-- explodes under the watermark-pair parser encoding).
parseAttrDef-roundtrip :
    ∀ (d : AttrDef) (pos : Position) (outer-suffix : List Char)
  → WfAttrDef-NotRel d
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrDef pos (emitAttrDef-chars d ++ₗ outer-suffix))
    ≡ just (mkResult d
             (advancePositions pos (emitAttrDef-chars d))
             outer-suffix)
parseAttrDef-roundtrip
  (mkAttrDef n ASNetwork ty) pos outer-suffix (Wf-Network wf-ty) nl-stop =
    subst₂ (λ sc ty' →
             proj₂ (parseAttrDef pos
               (emitAttrDef-chars (mkAttrDef n sc ty') ++ₗ outer-suffix))
             ≡ just (mkResult (mkAttrDef n sc ty')
                      (advancePositions pos
                        (emitAttrDef-chars (mkAttrDef n sc ty')))
                      outer-suffix))
           scope-eq
           (liftAttrType-rawAttrTypeOf wf-ty)
           (parseAttrDef-roundtrip-raw pos RssNet n (rawAttrTypeOf wf-ty)
                                        outer-suffix nl-stop)
    where
      scope-eq : liftStdScope RssNet ≡ ASNetwork
      scope-eq = refl
parseAttrDef-roundtrip
  (mkAttrDef n ASNode ty) pos outer-suffix (Wf-Node wf-ty) nl-stop =
    subst₂ (λ sc ty' →
             proj₂ (parseAttrDef pos
               (emitAttrDef-chars (mkAttrDef n sc ty') ++ₗ outer-suffix))
             ≡ just (mkResult (mkAttrDef n sc ty')
                      (advancePositions pos
                        (emitAttrDef-chars (mkAttrDef n sc ty')))
                      outer-suffix))
           scope-eq
           (liftAttrType-rawAttrTypeOf wf-ty)
           (parseAttrDef-roundtrip-raw pos RssNode n (rawAttrTypeOf wf-ty)
                                        outer-suffix nl-stop)
    where
      scope-eq : liftStdScope RssNode ≡ ASNode
      scope-eq = refl
parseAttrDef-roundtrip
  (mkAttrDef n ASMessage ty) pos outer-suffix (Wf-Message wf-ty) nl-stop =
    subst₂ (λ sc ty' →
             proj₂ (parseAttrDef pos
               (emitAttrDef-chars (mkAttrDef n sc ty') ++ₗ outer-suffix))
             ≡ just (mkResult (mkAttrDef n sc ty')
                      (advancePositions pos
                        (emitAttrDef-chars (mkAttrDef n sc ty')))
                      outer-suffix))
           scope-eq
           (liftAttrType-rawAttrTypeOf wf-ty)
           (parseAttrDef-roundtrip-raw pos RssMsg n (rawAttrTypeOf wf-ty)
                                        outer-suffix nl-stop)
    where
      scope-eq : liftStdScope RssMsg ≡ ASMessage
      scope-eq = refl
parseAttrDef-roundtrip
  (mkAttrDef n ASSignal ty) pos outer-suffix (Wf-Signal wf-ty) nl-stop =
    subst₂ (λ sc ty' →
             proj₂ (parseAttrDef pos
               (emitAttrDef-chars (mkAttrDef n sc ty') ++ₗ outer-suffix))
             ≡ just (mkResult (mkAttrDef n sc ty')
                      (advancePositions pos
                        (emitAttrDef-chars (mkAttrDef n sc ty')))
                      outer-suffix))
           scope-eq
           (liftAttrType-rawAttrTypeOf wf-ty)
           (parseAttrDef-roundtrip-raw pos RssSig n (rawAttrTypeOf wf-ty)
                                        outer-suffix nl-stop)
    where
      scope-eq : liftStdScope RssSig ≡ ASSignal
      scope-eq = refl
parseAttrDef-roundtrip
  (mkAttrDef n ASEnvVar ty) pos outer-suffix (Wf-EnvVar wf-ty) nl-stop =
    subst₂ (λ sc ty' →
             proj₂ (parseAttrDef pos
               (emitAttrDef-chars (mkAttrDef n sc ty') ++ₗ outer-suffix))
             ≡ just (mkResult (mkAttrDef n sc ty')
                      (advancePositions pos
                        (emitAttrDef-chars (mkAttrDef n sc ty')))
                      outer-suffix))
           scope-eq
           (liftAttrType-rawAttrTypeOf wf-ty)
           (parseAttrDef-roundtrip-raw pos RssEnv n (rawAttrTypeOf wf-ty)
                                        outer-suffix nl-stop)
    where
      scope-eq : liftStdScope RssEnv ≡ ASEnvVar
      scope-eq = refl

-- ============================================================================
-- SLIM `parseAttrDefRel-roundtrip` — rel scope variant
-- ============================================================================

private
  parseAttrDefRel-roundtrip-raw :
      ∀ (pos : Position) (s : RawRelScope) (n : List Char) (rt : RawAttrType)
        (outer-suffix : List Char)
    → SuffixStops isNewlineStart outer-suffix
    → proj₂ (parseAttrDefRel pos
        (emitAttrDef-chars (mkAttrDef n (liftRelScope s) (liftAttrType rt))
         ++ₗ outer-suffix))
      ≡ just (mkResult (mkAttrDef n (liftRelScope s) (liftAttrType rt))
               (advancePositions pos
                 (emitAttrDef-chars
                   (mkAttrDef n (liftRelScope s) (liftAttrType rt))))
               outer-suffix)
  parseAttrDefRel-roundtrip-raw pos s n rt outer-suffix nl-stop =
    trans (cong (λ inp → proj₂ (parseAttrDefRel pos (inp ++ₗ outer-suffix)))
                (sym bridge))
      (trans step-format
        (trans step-many-newline step-pure))
    where
      d : AttrDef
      d = mkAttrDef n (liftRelScope s) (liftAttrType rt)

      bridge : emit attrDefRelFmt (s , n , rt , tt) ≡ emitAttrDef-chars d
      bridge = emit-attrDefRelFmt-eq-emitAttrDef-chars s n rt

      pos-line : Position
      pos-line = advancePositions pos (emit attrDefRelFmt (s , n , rt , tt))

      cont-line : FmtAD.RelAttrDefCarrier → Parser AttrDef
      cont-line c = many parseNewline >>= λ _ → pure (liftRelAttrDef c)

      cont-blanks : List Char → Parser AttrDef
      cont-blanks _ = pure (liftRelAttrDef (s , n , rt , tt))

      step-format :
        proj₂ (parseAttrDefRel pos
                (emit attrDefRelFmt (s , n , rt , tt) ++ₗ outer-suffix))
        ≡ proj₂ (cont-line (s , n , rt , tt) pos-line outer-suffix)
      step-format =
        bind-just-step (parse attrDefRelFmt) cont-line
                       pos (emit attrDefRelFmt (s , n , rt , tt) ++ₗ outer-suffix)
                       (s , n , rt , tt) pos-line outer-suffix
                       (parseAttrDefRel-format-roundtrip pos s n rt outer-suffix)

      step-many-newline :
        proj₂ (cont-line (s , n , rt , tt) pos-line outer-suffix)
        ≡ proj₂ (cont-blanks [] pos-line outer-suffix)
      step-many-newline =
        bind-just-step (many parseNewline) cont-blanks
                       pos-line outer-suffix
                       [] pos-line outer-suffix
                       (manyHelper-parseNewline-exhaust
                         pos-line outer-suffix (length outer-suffix) nl-stop)

      step-pure :
        proj₂ (cont-blanks [] pos-line outer-suffix)
        ≡ just (mkResult d
                 (advancePositions pos (emitAttrDef-chars d))
                 outer-suffix)
      step-pure =
        cong (λ p → just (mkResult d p outer-suffix))
             (cong (advancePositions pos) bridge)

parseAttrDefRel-roundtrip :
    ∀ (d : AttrDef) (pos : Position) (outer-suffix : List Char)
  → WfAttrDef-Rel d
  → SuffixStops isNewlineStart outer-suffix
  → proj₂ (parseAttrDefRel pos (emitAttrDef-chars d ++ₗ outer-suffix))
    ≡ just (mkResult d
             (advancePositions pos (emitAttrDef-chars d))
             outer-suffix)
parseAttrDefRel-roundtrip
  (mkAttrDef n ASNodeMsg ty) pos outer-suffix (Wf-NodeMsg wf-ty) nl-stop =
    subst₂ (λ sc ty' →
             proj₂ (parseAttrDefRel pos
               (emitAttrDef-chars (mkAttrDef n sc ty') ++ₗ outer-suffix))
             ≡ just (mkResult (mkAttrDef n sc ty')
                      (advancePositions pos
                        (emitAttrDef-chars (mkAttrDef n sc ty')))
                      outer-suffix))
           scope-eq
           (liftAttrType-rawAttrTypeOf wf-ty)
           (parseAttrDefRel-roundtrip-raw pos RrsNodeMsg n
                                           (rawAttrTypeOf wf-ty)
                                           outer-suffix nl-stop)
    where
      scope-eq : liftRelScope RrsNodeMsg ≡ ASNodeMsg
      scope-eq = refl
parseAttrDefRel-roundtrip
  (mkAttrDef n ASNodeSig ty) pos outer-suffix (Wf-NodeSig wf-ty) nl-stop =
    subst₂ (λ sc ty' →
             proj₂ (parseAttrDefRel pos
               (emitAttrDef-chars (mkAttrDef n sc ty') ++ₗ outer-suffix))
             ≡ just (mkResult (mkAttrDef n sc ty')
                      (advancePositions pos
                        (emitAttrDef-chars (mkAttrDef n sc ty')))
                      outer-suffix))
           scope-eq
           (liftAttrType-rawAttrTypeOf wf-ty)
           (parseAttrDefRel-roundtrip-raw pos RrsNodeSig n
                                           (rawAttrTypeOf wf-ty)
                                           outer-suffix nl-stop)
    where
      scope-eq : liftRelScope RrsNodeSig ≡ ASNodeSig
      scope-eq = refl
