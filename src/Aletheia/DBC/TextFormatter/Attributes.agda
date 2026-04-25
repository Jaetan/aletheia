{-# OPTIONS --safe --without-K #-}

-- Attribute emitters for the DBC text format (Phase B.3.c.5; layer-1 form
-- 2026-04-24).
--
-- Grammar slice emitted (mirrors `TextParser.Attributes`):
--   attr-def     ::= "BA_DEF_" (ws attr-scope)? ws string-lit ws attr-type
--                    ws? ";" newline
--   attr-def-rel ::= "BA_DEF_REL_" ws rel-scope ws string-lit ws attr-type
--                    ws? ";" newline
--   attr-default ::= "BA_DEF_DEF_" ws string-lit ws attr-value ws? ";" newline
--   attr-assign  ::= "BA_" ws string-lit (ws attr-target)? ws attr-value
--                    ws? ";" newline
--   attr-rel     ::= "BA_REL_" ws string-lit ws rel-target ws attr-value
--                    ws? ";" newline
--
-- Enum-wire asymmetry on emit:
--   * `AVEnum n` inside an `AttrDefault` emits the *label at index n* in
--     the matching AttrDef's ENUM labels list, quoted as a string literal.
--     This mirrors `TextParser.Attributes.refineDefaultValue`'s label→index
--     lookup in the opposite direction.  Emission requires the ambient
--     AttrDef list, so `emitAttrDefault-chars` takes it as a parameter.
--   * `AVEnum n` inside an `AttrAssign` emits `n` directly as a decimal
--     integer (no lookup, no quoting).
--   Any other AttrValue constructor (`AVInt` / `AVFloat` / `AVString` /
--   `AVHex`) emits identically in both contexts.
--
-- Lookup-table discipline: `emitAttributes-chars` precomputes the AttrDef
-- list via `collectDefs` and threads it into every per-attribute emit.
-- An earlier design threaded a mutable state-like accumulator through a
-- fold; the precompute approach is order-insensitive (works for hand-
-- written DBCs where defs may interleave with defaults), and forces the
-- missing-def case to be handled at compile time in `emitDefaultValue-chars`.
--
-- Canonical choices (cantools parity):
--   * Separator whitespace — single space between every token.  The
--     corpus fixture exercises cantools' double-space quirks after
--     `BA_DEF_DEF_`, after `BU_BO_REL_` / `BU_SG_REL_`, and after `ENUM`;
--     the parser accepts both (via `parseWS = some (satisfy isHSpace)`),
--     and this emitter canonicalises to single-space on output.  The
--     roundtrip `parseText ∘ formatText ≡ id` (B.3.d) composes either way.
--   * Trailing semicolon — cantools' historical convention prefixes `;`
--     with a space on `BA_DEF_*` lines (`" ;\n"`) but not on `BA_DEF_DEF_`
--     or `BA_` / `BA_REL_` lines (`";\n"`).  Mirrored here.
--   * Missing/OOB enum label — when `AVEnum n` inside a default has no
--     matching AttrDef, or the index overflows the label list, emit
--     `""` (empty string literal) as a clearly-wrong sentinel.
--
-- All emitters are `List Char`-valued (B.3.d Option 3a layer-1 layout —
-- see `Emitter` module header).
module Aletheia.DBC.TextFormatter.Attributes where
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.Types using (attrDefNameStr; attrDefaultNameStr; attrAssignNameStr)
open import Aletheia.DBC.DecRat.Refinement using (intDecRatToℤ; natDecRatToℕ)

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; foldr) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.String using (String; toList)
open import Data.String.Properties using () renaming (_≟_ to _≟ₛ_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Aletheia.DBC.Types using
  ( AttrScope; ASNetwork; ASNode; ASMessage; ASSignal; ASEnvVar
  ; ASNodeMsg; ASNodeSig
  ; AttrType; ATInt; ATFloat; ATString; ATEnum; ATHex
  ; AttrValue; AVInt; AVFloat; AVString; AVEnum; AVHex
  ; AttrTarget; ATgtNetwork; ATgtNode; ATgtMessage; ATgtSignal
  ; ATgtEnvVar; ATgtNodeMsg; ATgtNodeSig
  ; AttrDef; AttrDefault; AttrAssign
  ; DBCAttribute; DBCAttrDef; DBCAttrDefault; DBCAttrAssign
  )

open import Aletheia.DBC.TextFormatter.Emitter using
  (showℕ-dec-chars; showℤ-dec-chars; showDecRat-dec-chars; quoteStringLit-chars)
open import Aletheia.DBC.TextFormatter.Topology using (rawCanIdℕ)

-- ============================================================================
-- DEF LOOKUP TABLE (shared across defaults in `emitAttributes-chars`)
-- ============================================================================

-- Extract every AttrDef from a DBCAttribute list, preserving wire order.
collectDefs : List DBCAttribute → List AttrDef
collectDefs [] = []
collectDefs (DBCAttrDef d     ∷ rest) = d ∷ collectDefs rest
collectDefs (DBCAttrDefault _ ∷ rest) = collectDefs rest
collectDefs (DBCAttrAssign _  ∷ rest) = collectDefs rest

-- Linear scan (small def counts in practice — single digits in corpus).
lookupDef : String → List AttrDef → Maybe AttrDef
lookupDef _ [] = nothing
lookupDef name (d ∷ rest) =
  if ⌊ name ≟ₛ attrDefNameStr d ⌋
    then just d
    else lookupDef name rest

-- Nth element lookup, returns `""` on out-of-bounds (matches the
-- graceful-degradation contract for `AVEnum` defaults).
nthLabel : ℕ → List String → String
nthLabel _       []       = ""
nthLabel zero    (x ∷ _)  = x
nthLabel (suc n) (_ ∷ xs) = nthLabel n xs

-- ============================================================================
-- SCOPE / TYPE / TARGET EMITTERS
-- ============================================================================

-- Scope keyword emitted between `BA_DEF_` / `BA_DEF_REL_` and the name,
-- with trailing space.  `ASNetwork` emits `[]` so `BA_DEF_ "name" ...`
-- falls out naturally; the other six keywords carry their canonical DBC
-- token followed by a single space.
emitScopePrefix-chars : AttrScope → List Char
emitScopePrefix-chars ASNetwork = []
emitScopePrefix-chars ASNode    = toList "BU_ "
emitScopePrefix-chars ASMessage = toList "BO_ "
emitScopePrefix-chars ASSignal  = toList "SG_ "
emitScopePrefix-chars ASEnvVar  = toList "EV_ "
emitScopePrefix-chars ASNodeMsg = toList "BU_BO_REL_ "
emitScopePrefix-chars ASNodeSig = toList "BU_SG_REL_ "

-- Relation scopes dispatch to `BA_DEF_REL_`; everything else to `BA_DEF_`.
isRelScope : AttrScope → Bool
isRelScope ASNodeMsg = true
isRelScope ASNodeSig = true
isRelScope _         = false

-- Enum labels comma-separated, each quoted.  Matches cantools output of
-- `"Low","Normal","High"` (no spaces around comma).
emitEnumLabels-chars : List String → List Char
emitEnumLabels-chars []       = []
emitEnumLabels-chars (x ∷ xs) =
  quoteStringLit-chars x ++ₗ
  foldr (λ y acc → ',' ∷ quoteStringLit-chars y ++ₗ acc) [] xs

emitAttrType-chars : AttrType → List Char
emitAttrType-chars (ATInt mn mx)   =
  toList "INT "   ++ₗ showℤ-dec-chars (intDecRatToℤ mn) ++ₗ
  ' ' ∷ showℤ-dec-chars (intDecRatToℤ mx)
emitAttrType-chars (ATFloat mn mx) =
  toList "FLOAT " ++ₗ showDecRat-dec-chars mn ++ₗ
  ' ' ∷ showDecRat-dec-chars mx
emitAttrType-chars ATString        = toList "STRING"
emitAttrType-chars (ATEnum labels) =
  toList "ENUM "  ++ₗ emitEnumLabels-chars labels
emitAttrType-chars (ATHex mn mx)   =
  toList "HEX "   ++ₗ showℕ-dec-chars (natDecRatToℕ mn) ++ₗ
  ' ' ∷ showℕ-dec-chars (natDecRatToℕ mx)

-- ============================================================================
-- VALUE EMITTERS
-- ============================================================================

-- Assignment context: `AVEnum n` → decimal integer (no label lookup).
emitAssignValue-chars : AttrValue → List Char
emitAssignValue-chars (AVInt z)    = showℤ-dec-chars (intDecRatToℤ z)
emitAssignValue-chars (AVFloat q)  = showDecRat-dec-chars q
emitAssignValue-chars (AVString s) = quoteStringLit-chars s
emitAssignValue-chars (AVEnum n)   = showℕ-dec-chars (natDecRatToℕ n)
emitAssignValue-chars (AVHex n)    = showℕ-dec-chars (natDecRatToℕ n)

-- Default context: `AVEnum n` → look up the label at index n in the
-- matching AttrDef's ENUM labels, quoted as a string literal.  Missing
-- def, non-ENUM def, or OOB index all degrade to `""` (see module header).
emitDefaultValue-chars : List AttrDef → (attrName : String) → AttrValue → List Char
emitDefaultValue-chars _    _  (AVInt z)    = showℤ-dec-chars (intDecRatToℤ z)
emitDefaultValue-chars _    _  (AVFloat q)  = showDecRat-dec-chars q
emitDefaultValue-chars _    _  (AVString s) = quoteStringLit-chars s
emitDefaultValue-chars _    _  (AVHex n)    = showℕ-dec-chars (natDecRatToℕ n)
emitDefaultValue-chars defs nm (AVEnum n) with lookupDef nm defs
... | nothing  = quoteStringLit-chars ""
... | just def with AttrDef.attrType def
...   | ATEnum labels = quoteStringLit-chars (nthLabel (natDecRatToℕ n) labels)
...   | _             = quoteStringLit-chars ""

-- ============================================================================
-- LINE EMITTERS
-- ============================================================================

-- `"BA_DEF_" ws (attr-scope ws)? string-lit ws attr-type ws? ";" newline`
-- vs `"BA_DEF_REL_" ws rel-scope ws string-lit ws attr-type ws? ";" newline`,
-- dispatched on scope.  Trailing ` ;\n` (space before semicolon) matches
-- the cantools BA_DEF_* convention; the shorter-line families use `;\n`
-- (no space).
emitAttrDef-chars : AttrDef → List Char
emitAttrDef-chars d with isRelScope (AttrDef.scope d)
... | true  =
  toList "BA_DEF_REL_ " ++ₗ emitScopePrefix-chars (AttrDef.scope d) ++ₗ
  quoteStringLit-chars (attrDefNameStr d) ++ₗ
  ' ' ∷ emitAttrType-chars (AttrDef.attrType d) ++ₗ toList " ;\n"
... | false =
  toList "BA_DEF_ " ++ₗ emitScopePrefix-chars (AttrDef.scope d) ++ₗ
  quoteStringLit-chars (attrDefNameStr d) ++ₗ
  ' ' ∷ emitAttrType-chars (AttrDef.attrType d) ++ₗ toList " ;\n"

-- `"BA_DEF_DEF_" ws string-lit ws attr-value ws? ";" newline`.  The
-- ambient AttrDef list flows in for ENUM label resolution.
emitAttrDefault-chars : List AttrDef → AttrDefault → List Char
emitAttrDefault-chars defs d =
  toList "BA_DEF_DEF_ " ++ₗ
  quoteStringLit-chars (attrDefaultNameStr d) ++ₗ
  ' ' ∷ emitDefaultValue-chars defs (attrDefaultNameStr d) (AttrDefault.value d) ++ₗ
  toList ";\n"

-- `"BA_" ...` vs `"BA_REL_" ...` dispatched on the target.  For each
-- target shape the explicit cases spell out the inter-token spacing
-- directly rather than routing through an `emitAttrTarget`; this keeps
-- the assembly of the line simple and avoids the "target-is-network ⇒ no
-- trailing space" special case that a uniform helper would need.
emitAttrAssign-chars : AttrAssign → List Char
emitAttrAssign-chars a = body (AttrAssign.target a)
  where
    qname : List Char
    qname = quoteStringLit-chars (attrAssignNameStr a)
    vstr : List Char
    vstr = emitAssignValue-chars (AttrAssign.value a)
    body : AttrTarget → List Char
    body ATgtNetwork =
      toList "BA_ " ++ₗ qname ++ₗ ' ' ∷ vstr ++ₗ toList ";\n"
    body (ATgtNode n) =
      toList "BA_ " ++ₗ qname ++ₗ toList " BU_ " ++ₗ toList (Identifier.name n) ++ₗ
      ' ' ∷ vstr ++ₗ toList ";\n"
    body (ATgtMessage cid) =
      toList "BA_ " ++ₗ qname ++ₗ toList " BO_ " ++ₗ
      showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
      ' ' ∷ vstr ++ₗ toList ";\n"
    body (ATgtSignal cid sig) =
      toList "BA_ " ++ₗ qname ++ₗ toList " SG_ " ++ₗ
      showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
      ' ' ∷ toList (Identifier.name sig) ++ₗ ' ' ∷ vstr ++ₗ toList ";\n"
    body (ATgtEnvVar ev) =
      toList "BA_ " ++ₗ qname ++ₗ toList " EV_ " ++ₗ toList (Identifier.name ev) ++ₗ
      ' ' ∷ vstr ++ₗ toList ";\n"
    body (ATgtNodeMsg n cid) =
      toList "BA_REL_ " ++ₗ qname ++ₗ toList " BU_BO_REL_ " ++ₗ
      toList (Identifier.name n) ++ₗ ' ' ∷
      showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
      ' ' ∷ vstr ++ₗ toList ";\n"
    body (ATgtNodeSig n cid sig) =
      toList "BA_REL_ " ++ₗ qname ++ₗ toList " BU_SG_REL_ " ++ₗ
      toList (Identifier.name n) ++ₗ toList " SG_ " ++ₗ
      showℕ-dec-chars (rawCanIdℕ cid) ++ₗ
      ' ' ∷ toList (Identifier.name sig) ++ₗ ' ' ∷ vstr ++ₗ toList ";\n"

-- ============================================================================
-- SECTION EMITTER
-- ============================================================================

emitAttribute-chars : List AttrDef → DBCAttribute → List Char
emitAttribute-chars _    (DBCAttrDef d)     = emitAttrDef-chars d
emitAttribute-chars defs (DBCAttrDefault d) = emitAttrDefault-chars defs d
emitAttribute-chars _    (DBCAttrAssign a)  = emitAttrAssign-chars a

-- Precompute the def lookup table once per `emitAttributes-chars` call
-- and thread it through the per-line fold.  Empty list emits `[]` (no
-- attributes section), matching cantools behaviour on attribute-free
-- databases.
emitAttributes-chars : List DBCAttribute → List Char
emitAttributes-chars attrs =
  let defs = collectDefs attrs
  in foldr (λ a acc → emitAttribute-chars defs a ++ₗ acc) [] attrs
