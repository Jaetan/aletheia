-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Universal-attribute roundtrip dispatcher for the
-- `DBCAttrDefault` shape.  (Bisecting heap blowup: AVString-only.)
module Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Attribute.Default where

open import Data.Char  using (Char)
open import Data.Integer using (+_)
open import Data.List  using (List; _∷_)
  renaming (_++_ to _++ₗ_)
open import Data.List.Properties using ()
  renaming (++-assoc to ++ₗ-assoc)
open import Data.Maybe using (just)
open import Data.Product using (proj₂)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Aletheia.Parser.Combinators using
  (Position; mkResult; advancePositions)

open import Aletheia.DBC.DecRat using (DecRat; fromℤ)
open import Aletheia.DBC.DecRat.Refinement using
  ( IntDecRat; NatDecRat
  ; intDecRatToℤ; natDecRatToℕ
  ; fromℤ-intDecRatToℤ
  ; fromℕ-natDecRatToℕ
  )
open import Aletheia.DBC.Types using
  ( ATEnum
  ; AttrDef; mkAttrDef
  ; AVString; AVFloat; AVInt; AVHex; AVEnum
  ; AttrDefault; mkAttrDefault
  ; DBCAttrDefault
  )

open import Aletheia.DBC.TextFormatter.Attributes using
  ( emitAttribute-chars
  ; emitDefaultValue-chars
  ; nthLabel
  )
open import Aletheia.DBC.TextFormatter.Emitter using
  ( quoteStringLit-chars
  ; showDecRat-dec-chars
  ; showInt-chars
  ; showℕ-dec-chars
  )

open import Aletheia.DBC.TextParser.Attributes using
  ( RawDefault; mkRawAttrDefault
  ; RavString; RavDecRat
  ; parseAttrLine
  ; lookupDef
  )

open import Aletheia.DBC.TextParser.Properties.Aggregator.Foundations using
  (rawOf; WFAttribute; wfDefault)
open import Aletheia.DBC.TextParser.Properties.Attributes.Common using
  (VMTEnum)

open import Aletheia.DBC.TextParser.Properties.Attributes.Line using
  ( parseAttrLine-roundtrip-RawDefault-RavString
  ; parseAttrLine-roundtrip-RawDefault-RavDecRatFrac
  ; parseAttrLine-roundtrip-RawDefault-RavDecRatBareInt
  )
open import Aletheia.DBC.TextParser.Properties.Attributes.Default using
  (module Trace)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart)

private
  trail-bridge :
      ∀ (V outer : List Char)
    → (' ' ∷ V ++ₗ toList ";\n") ++ₗ outer
      ≡ ' ' ∷ V ++ₗ toList ";\n" ++ₗ outer
  trail-bridge V outer =
    cong (' ' ∷_) (++ₗ-assoc V (toList ";\n") outer)

  default-input-bridge :
      ∀ (name vstr outer : List Char)
    → (toList "BA_DEF_DEF_ " ++ₗ quoteStringLit-chars name ++ₗ
         ' ' ∷ vstr ++ₗ toList ";\n") ++ₗ outer
      ≡ toList "BA_DEF_DEF_ " ++ₗ quoteStringLit-chars name ++ₗ
         ' ' ∷ vstr ++ₗ toList ";\n" ++ₗ outer
  default-input-bridge name vstr outer =
    trans (++ₗ-assoc (toList "BA_DEF_DEF_ ") _ outer)
      (cong (toList "BA_DEF_DEF_ " ++ₗ_)
        (trans (++ₗ-assoc (quoteStringLit-chars name) _ outer)
          (cong (quoteStringLit-chars name ++ₗ_)
                (trail-bridge vstr outer))))

  -- Per-shape bridges restate `default-input-bridge` with the literal
  -- `emitAttribute-chars … ++ₗ outer` term as the LHS.  Under the pair
  -- encoding the subst target must be SYNTACTICALLY the declared goal —
  -- otherwise conversion checking whnf-unfolds `parseAttrLine` on the
  -- symbolic input (heap blowup past the 16G gate cap).  The restatement
  -- itself only costs a list-level `emit` unfold.

  emit-bridge-AVString :
      ∀ (defs : List AttrDef) (name s outer : List Char)
    → emitAttribute-chars defs
        (DBCAttrDefault (mkAttrDefault name (AVString s)))
      ++ₗ outer
      ≡ toList "BA_DEF_DEF_ " ++ₗ quoteStringLit-chars name ++ₗ
         ' ' ∷ quoteStringLit-chars s ++ₗ toList ";\n" ++ₗ outer
  emit-bridge-AVString defs name s outer =
    default-input-bridge name (quoteStringLit-chars s) outer

  emit-bridge-AVFloat :
      ∀ (defs : List AttrDef) (name : List Char) (d : DecRat)
        (outer : List Char)
    → emitAttribute-chars defs
        (DBCAttrDefault (mkAttrDefault name (AVFloat d)))
      ++ₗ outer
      ≡ toList "BA_DEF_DEF_ " ++ₗ quoteStringLit-chars name ++ₗ
         ' ' ∷ showDecRat-dec-chars d ++ₗ toList ";\n" ++ₗ outer
  emit-bridge-AVFloat defs name d outer =
    default-input-bridge name (showDecRat-dec-chars d) outer

  emit-bridge-AVInt :
      ∀ (defs : List AttrDef) (name : List Char) (z' : IntDecRat)
        (outer : List Char)
    → emitAttribute-chars defs
        (DBCAttrDefault (mkAttrDefault name (AVInt z')))
      ++ₗ outer
      ≡ toList "BA_DEF_DEF_ " ++ₗ quoteStringLit-chars name ++ₗ
         ' ' ∷ showInt-chars (intDecRatToℤ z') ++ₗ toList ";\n" ++ₗ outer
  emit-bridge-AVInt defs name z' outer =
    default-input-bridge name (showInt-chars (intDecRatToℤ z')) outer

  -- The AVHex bridge is stated in the BareInt lemma's `showInt-chars (+ m)`
  -- spelling (not the emit-side `showℕ-dec-chars m`): both reduce to
  -- `showNat-chars m`, and absorbing that alias here keeps every
  -- `parseAttrLine`-input subst a whole-input abstraction — a motive that
  -- abstracts INSIDE the ++-chain lets conversion unfold the parser over
  -- the concrete prefix (heap blowup).  The alias costs only a list-level
  -- reduction in this bridge's own type-check.
  emit-bridge-AVHex :
      ∀ (defs : List AttrDef) (name : List Char) (n : NatDecRat)
        (outer : List Char)
    → emitAttribute-chars defs
        (DBCAttrDefault (mkAttrDefault name (AVHex n)))
      ++ₗ outer
      ≡ toList "BA_DEF_DEF_ " ++ₗ quoteStringLit-chars name ++ₗ
         ' ' ∷ showInt-chars (+ natDecRatToℕ n) ++ₗ toList ";\n" ++ₗ outer
  emit-bridge-AVHex defs name n outer =
    default-input-bridge name (showInt-chars (+ natDecRatToℕ n)) outer

  on-AVString :
      ∀ (defs : List AttrDef) (pos : Position) (name : List Char)
        (s : List Char) (outer : List Char)
    → SuffixStops isNewlineStart outer
    → proj₂ (parseAttrLine pos
        (emitAttribute-chars defs
           (DBCAttrDefault (mkAttrDefault name (AVString s)))
         ++ₗ outer))
      ≡ just (mkResult
                (RawDefault (mkRawAttrDefault name (RavString s)))
                (Trace.pos8 pos name (quoteStringLit-chars s) outer)
                outer)
  on-AVString defs pos name s outer ss-NL =
    subst
      (λ inp → proj₂ (parseAttrLine pos inp) ≡
                just (mkResult
                        (RawDefault (mkRawAttrDefault name (RavString s)))
                        (Trace.pos8 pos name (quoteStringLit-chars s) outer)
                        outer))
      (sym (emit-bridge-AVString defs name s outer))
      (parseAttrLine-roundtrip-RawDefault-RavString
         pos name s outer ss-NL)

  on-AVFloat :
      ∀ (defs : List AttrDef) (pos : Position) (name : List Char)
        (d : DecRat) (outer : List Char)
    → SuffixStops isNewlineStart outer
    → proj₂ (parseAttrLine pos
        (emitAttribute-chars defs
           (DBCAttrDefault (mkAttrDefault name (AVFloat d)))
         ++ₗ outer))
      ≡ just (mkResult
                (RawDefault (mkRawAttrDefault name (RavDecRat d)))
                (Trace.pos8 pos name (showDecRat-dec-chars d) outer)
                outer)
  on-AVFloat defs pos name d outer ss-NL =
    subst
      (λ inp → proj₂ (parseAttrLine pos inp) ≡
                just (mkResult
                        (RawDefault (mkRawAttrDefault name (RavDecRat d)))
                        (Trace.pos8 pos name (showDecRat-dec-chars d) outer)
                        outer))
      (sym (emit-bridge-AVFloat defs name d outer))
      (parseAttrLine-roundtrip-RawDefault-RavDecRatFrac
         pos name d outer ss-NL)

  on-AVInt :
      ∀ (defs : List AttrDef) (pos : Position) (name : List Char)
        (z' : IntDecRat) (outer : List Char)
    → SuffixStops isNewlineStart outer
    → proj₂ (parseAttrLine pos
        (emitAttribute-chars defs
           (DBCAttrDefault (mkAttrDefault name (AVInt z')))
         ++ₗ outer))
      ≡ just (mkResult
                (RawDefault (mkRawAttrDefault name
                               (RavDecRat (IntDecRat.value z'))))
                (Trace.pos8 pos name (showInt-chars (intDecRatToℤ z')) outer)
                outer)
  on-AVInt defs pos name z' outer ss-NL =
    subst
      (λ q → proj₂ (parseAttrLine pos
                (emitAttribute-chars defs
                   (DBCAttrDefault (mkAttrDefault name (AVInt z')))
                 ++ₗ outer))
               ≡ just (mkResult
                         (RawDefault (mkRawAttrDefault name (RavDecRat q)))
                         (Trace.pos8 pos name
                            (showInt-chars (intDecRatToℤ z')) outer)
                         outer))
      (fromℤ-intDecRatToℤ z')
      (subst
         (λ inp → proj₂ (parseAttrLine pos inp) ≡
                   just (mkResult
                           (RawDefault (mkRawAttrDefault name
                                          (RavDecRat (fromℤ (intDecRatToℤ z')))))
                           (Trace.pos8 pos name
                              (showInt-chars (intDecRatToℤ z')) outer)
                           outer))
         (sym (emit-bridge-AVInt defs name z' outer))
         (parseAttrLine-roundtrip-RawDefault-RavDecRatBareInt
            pos name (intDecRatToℤ z') outer ss-NL))

  on-AVHex :
      ∀ (defs : List AttrDef) (pos : Position) (name : List Char)
        (n : NatDecRat) (outer : List Char)
    → SuffixStops isNewlineStart outer
    → proj₂ (parseAttrLine pos
        (emitAttribute-chars defs
           (DBCAttrDefault (mkAttrDefault name (AVHex n)))
         ++ₗ outer))
      ≡ just (mkResult
                (RawDefault (mkRawAttrDefault name
                               (RavDecRat (NatDecRat.value n))))
                (Trace.pos8 pos name (showℕ-dec-chars (natDecRatToℕ n)) outer)
                outer)
  -- Both motives keep the position in the lemma's `showInt-chars (+ m)`
  -- spelling; the declared `showℕ-dec-chars` form differs only there, and
  -- that final alignment is a Position-level reduction (advancePositions
  -- walk), never a parser unfold.
  on-AVHex defs pos name n outer ss-NL =
    subst
      (λ q → proj₂ (parseAttrLine pos
                (emitAttribute-chars defs
                   (DBCAttrDefault (mkAttrDefault name (AVHex n)))
                 ++ₗ outer))
               ≡ just (mkResult
                         (RawDefault (mkRawAttrDefault name (RavDecRat q)))
                         (Trace.pos8 pos name
                            (showInt-chars (+ natDecRatToℕ n)) outer)
                         outer))
      (fromℕ-natDecRatToℕ n)
      (subst
         (λ inp → proj₂ (parseAttrLine pos inp) ≡
                   just (mkResult
                           (RawDefault (mkRawAttrDefault name
                                          (RavDecRat (fromℤ (+ natDecRatToℕ n)))))
                           (Trace.pos8 pos name
                              (showInt-chars (+ natDecRatToℕ n)) outer)
                           outer))
         (sym (emit-bridge-AVHex defs name n outer))
         (parseAttrLine-roundtrip-RawDefault-RavDecRatBareInt
            pos name (+ natDecRatToℕ n) outer ss-NL))

  -- Small bridge lemmas decompose `emit` and `rawOf` for AVEnum-default into
  -- (a) outer structural shell — refl by `emitAttrDefault-chars` reduction;
  -- (b) `emitDefaultValue-chars` resolution under formatter-side `lookup-eq`
  --     — uses `with-on-equation` to thread the lookup result into the
  --     function's internal `with`-aux (external `rewrite` doesn't propagate
  --     into hidden aux blocks);
  -- (c) `rawOfDefaultValue-with-defs` resolution under parser-side `lookup-eq`.
  -- `emit-AVEnum-eq` and `rawOf-AVEnum-eq` then compose (a) + (b) / (a) + (c)
  -- via `cong`.

  emit-default-AVEnum-shell :
      ∀ (defs : List AttrDef) (name : List Char) (n : NatDecRat)
    → emitAttribute-chars defs (DBCAttrDefault (mkAttrDefault name (AVEnum n)))
      ≡ toList "BA_DEF_DEF_ " ++ₗ quoteStringLit-chars name ++ₗ
         ' ' ∷ emitDefaultValue-chars defs name (AVEnum n) ++ₗ toList ";\n"
  emit-default-AVEnum-shell _ _ _ = refl

  emit-default-value-AVEnum-eq :
      ∀ (defs : List AttrDef) (name : List Char) (n : NatDecRat)
        (defname : List Char) (defscope : _) (labels : List (List Char))
    → lookupDef name defs ≡ just (mkAttrDef defname defscope (ATEnum labels))
    → emitDefaultValue-chars defs name (AVEnum n)
      ≡ quoteStringLit-chars (nthLabel (natDecRatToℕ n) labels)
  emit-default-value-AVEnum-eq defs name n defname defscope labels fmt-lookup-eq
    with lookupDef name defs | fmt-lookup-eq
  ... | _ | refl = refl

  emit-AVEnum-eq :
      ∀ (defs : List AttrDef) (name : List Char) (n : NatDecRat)
        (defname : List Char) (defscope : _) (labels : List (List Char))
    → lookupDef name defs ≡ just (mkAttrDef defname defscope (ATEnum labels))
    → emitAttribute-chars defs (DBCAttrDefault (mkAttrDefault name (AVEnum n)))
      ≡ toList "BA_DEF_DEF_ " ++ₗ quoteStringLit-chars name ++ₗ
         ' ' ∷ quoteStringLit-chars (nthLabel (natDecRatToℕ n) labels) ++ₗ
         toList ";\n"
  emit-AVEnum-eq defs name n defname defscope labels parser-lookup-eq =
    trans (emit-default-AVEnum-shell defs name n)
      (cong (λ vstr → toList "BA_DEF_DEF_ " ++ₗ quoteStringLit-chars name ++ₗ
                       ' ' ∷ vstr ++ₗ toList ";\n")
            (emit-default-value-AVEnum-eq
               defs name n defname defscope labels parser-lookup-eq))

  rawOf-AVEnum-eq :
      ∀ (defs : List AttrDef) (name : List Char) (n : NatDecRat)
        (defname : List Char) (defscope : _) (labels : List (List Char))
    → lookupDef name defs ≡ just (mkAttrDef defname defscope (ATEnum labels))
    → rawOf defs (DBCAttrDefault (mkAttrDefault name (AVEnum n)))
      ≡ RawDefault (mkRawAttrDefault name
                      (RavString (nthLabel (natDecRatToℕ n) labels)))
  rawOf-AVEnum-eq defs name n defname defscope labels parser-lookup-eq
    with lookupDef name defs | parser-lookup-eq
  ... | _ | refl = refl

  on-AVEnum-with-ATEnum :
      ∀ (defs : List AttrDef) (pos : Position) (name : List Char) (n : NatDecRat)
        (defname : List Char) (defscope : _) (labels : List (List Char))
        (outer : List Char)
    → lookupDef name defs ≡ just (mkAttrDef defname defscope (ATEnum labels))
    → SuffixStops isNewlineStart outer
    → proj₂ (parseAttrLine pos
        (emitAttribute-chars defs
           (DBCAttrDefault (mkAttrDefault name (AVEnum n)))
         ++ₗ outer))
      ≡ just (mkResult
                (rawOf defs (DBCAttrDefault (mkAttrDefault name (AVEnum n))))
                (advancePositions pos
                   (emitAttribute-chars defs
                      (DBCAttrDefault (mkAttrDefault name (AVEnum n)))))
                outer)
  on-AVEnum-with-ATEnum defs pos name n defname defscope labels outer lookup-eq ss-NL =
    -- Step 1: get slim result with right-assoc input shape and slim-side RHS.
    -- Step 2: bridge LHS input via default-input-bridge (right-assoc → emit++outer).
    -- Step 3: bridge LHS emit form via sym emit-eq (slim-emit → universal-emit).
    -- Step 4: bridge RHS rawOf via sym rawOf-eq (slim-RHS → universal-rawOf).
    -- Step 5: bridge RHS position from Trace.pos8 to advancePositions pos universal-emit
    --         via cong (advancePositions pos) (sym emit-eq) (definitional reduction
    --         of `slim-emit-cons-form` = `slim-emit` is automatic).
    let emit-eq  = emit-AVEnum-eq  defs name n defname defscope labels lookup-eq
        rawOf-eq = rawOf-AVEnum-eq defs name n defname defscope labels lookup-eq
        v        = nthLabel (natDecRatToℕ n) labels
        cs-v     = quoteStringLit-chars v
        slim     = parseAttrLine-roundtrip-RawDefault-RavString
                     pos name v outer ss-NL
        -- slim : proj₂ (parseAttrLine pos (slim-emit-right-assoc ++ outer)) ≡
        --          just (mkResult (RawDefault (mkRawAttrDefault name (RavString v)))
        --                          (Trace.pos8 pos name cs-v outer) outer)
        bridged  = subst
                     (λ inp → proj₂ (parseAttrLine pos inp) ≡
                              just (mkResult
                                      (RawDefault (mkRawAttrDefault name
                                                     (RavString v)))
                                      (Trace.pos8 pos name cs-v outer)
                                      outer))
                     (sym (default-input-bridge name cs-v outer))
                     slim
        -- bridged : proj₂ (parseAttrLine pos (slim-emit ++ outer)) ≡ just-slim-RHS
        on-emit  = subst
                     (λ e → proj₂ (parseAttrLine pos (e ++ₗ outer)) ≡
                            just (mkResult
                                    (RawDefault (mkRawAttrDefault name
                                                   (RavString v)))
                                    (Trace.pos8 pos name cs-v outer)
                                    outer))
                     (sym emit-eq)
                     bridged
        -- on-emit : proj₂ (parseAttrLine pos (universal-emit ++ outer)) ≡ just-slim-RHS
        with-pos = trans on-emit
                     (cong
                       (λ pos9 →
                          just (mkResult
                                  (RawDefault (mkRawAttrDefault name (RavString v)))
                                  pos9 outer))
                       (cong (advancePositions pos) (sym emit-eq)))
        -- with-pos : proj₂ (parseAttrLine pos (universal-emit ++ outer)) ≡
        --              just (mkResult (RawDefault ...) (advancePositions pos universal-emit) outer)
    in trans with-pos
         (cong (λ r → just (mkResult r
                              (advancePositions pos
                                 (emitAttribute-chars defs
                                    (DBCAttrDefault
                                       (mkAttrDefault name (AVEnum n)))))
                              outer))
               (sym rawOf-eq))

-- ============================================================================
-- TOP-LEVEL DEFAULT DISPATCHER  (5-way on value)
-- ============================================================================
--
-- Pattern-matches on `AttrDefault.value`.  AVInt/AVFloat/AVString/AVHex are
-- universal in their value (no WF needed at this layer — the WFAttribute
-- precondition is consumed but unused for those four).  AVEnum requires WF
-- to extract the matching def + ATEnum labels.

parseAttrLine-on-emit-RawDefault :
    ∀ (defs : List AttrDef) (pos : Position)
      (d : AttrDefault) (outer : List Char)
  → WFAttribute defs (DBCAttrDefault d)
  → SuffixStops isNewlineStart outer
  → proj₂ (parseAttrLine pos
      (emitAttribute-chars defs (DBCAttrDefault d) ++ₗ outer))
    ≡ just (mkResult
              (rawOf defs (DBCAttrDefault d))
              (advancePositions pos
                 (emitAttribute-chars defs (DBCAttrDefault d)))
              outer)
parseAttrLine-on-emit-RawDefault defs pos
  (mkAttrDefault name (AVString s)) outer _ ss-NL =
    on-AVString defs pos name s outer ss-NL
parseAttrLine-on-emit-RawDefault defs pos
  (mkAttrDefault name (AVFloat d)) outer _ ss-NL =
    on-AVFloat defs pos name d outer ss-NL
parseAttrLine-on-emit-RawDefault defs pos
  (mkAttrDefault name (AVInt z')) outer _ ss-NL =
    on-AVInt defs pos name z' outer ss-NL
parseAttrLine-on-emit-RawDefault defs pos
  (mkAttrDefault name (AVHex n)) outer _ ss-NL =
    on-AVHex defs pos name n outer ss-NL
parseAttrLine-on-emit-RawDefault defs pos
  (mkAttrDefault name (AVEnum n)) outer
  (wfDefault _ (mkAttrDef defname defscope (ATEnum labels)) lookup-eq (VMTEnum _) _)
  ss-NL =
    on-AVEnum-with-ATEnum defs pos name n defname defscope labels outer
      lookup-eq ss-NL
