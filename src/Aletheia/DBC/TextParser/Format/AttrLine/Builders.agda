-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.5.d 3c-B sibling — L5 disjointness helpers and
-- KEYWORD-TARGET emit equations / L5 builders extracted from
-- `Format/AttrLine.agda` to keep the parent module below the 800-LOC
-- `feedback_properties_facade_split.md` trigger.
--
-- Pattern: external-consumer-redirect (R20 cluster Y's
-- `Properties/Aggregator/Refine/ValueDescriptions` split via `627ad25`).
-- This sibling imports from the parent for public types / Formats /
-- universal-roundtrip lemmas, plus the two names lifted private→public
-- in the same commit (`parseStdTgtL1-fails-on-non-keyword-head` and
-- `bridge-emit-tail`).  The 6 consumer Properties files
-- (Properties/Attributes/Assign/{Network,Node,Message,Signal,EnvVar,Rel}.agda)
-- split their `using` clause across both modules.

module Aletheia.DBC.TextParser.Format.AttrLine.Builders where

open import Data.Bool using (false)
open import Data.Char using (Char; _≈ᵇ_)
open import Data.List using (List; []; _∷_) renaming (_++_ to _++ₗ_)
open import Data.List.Properties using () renaming (++-assoc to ++ₗ-assoc)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_)
open import Data.String using (toList)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans; subst)

open import Aletheia.Parser.Combinators
  using (Position; mkResult; advancePositions)
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.TextParser.Lexer using (isHSpace)
open import Aletheia.DBC.TextParser.DecRatParse.Properties
  using (SuffixStops; ∷-stop; showNat-chars-head)
open import Aletheia.DBC.TextFormatter.Emitter
  using (digitChar; quoteStringLit-chars)
open import Aletheia.DBC.TextParser.Format
  using (nat; emit; parse; EmitsOK)
open import Aletheia.DBC.TextParser.Format.AttrValue
  using (RawAttrValueWire; attrValueWireFmt; digit-not-isHSpace)
open import Aletheia.DBC.TextParser.Format.AttrLine
  using ( stdTargetWireFmt; relTargetWireFmt
        ; RatwNet; RatwNode; RatwMsg; RatwSig; RatwEv
        ; RrtNodeMsg; RrtNodeSig
        ; attrAssignFmt; attrRelFmt
        ; parseAttrAssign-format-roundtrip
        ; parseStdTgtL1-fails-on-non-keyword-head
        ; bridge-emit-tail )

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
-- input.  All close by `refl` here — the parent `Format.AttrLine`'s
-- private internals (fwdStdTgt / bwdStdTgt / stdTargetWireCarrierFmt / arm
-- definitions) reduce through definitional unfolding regardless of
-- module-level `private` (which controls name export, not reduction).

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
