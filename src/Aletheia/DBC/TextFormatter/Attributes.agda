{-# OPTIONS --safe --without-K #-}

-- Attribute emitters for the DBC text format (Phase B.3.c.5).
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
--     AttrDef list, so `emitAttrDefault` takes it as a parameter.
--   * `AVEnum n` inside an `AttrAssign` emits `n` directly as a decimal
--     integer (no lookup, no quoting).
--   Any other AttrValue constructor (`AVInt` / `AVFloat` / `AVString` /
--   `AVHex`) emits identically in both contexts.
--
-- Lookup-table discipline: `emitAttributes` precomputes the AttrDef list
-- via `collectDefs` and threads it into every per-attribute emit.  An
-- earlier design threaded a mutable state-like accumulator through a
-- fold; the precompute approach is order-insensitive (works for hand-
-- written DBCs where defs may interleave with defaults), and forces the
-- missing-def case to be handled at compile time in `emitDefaultValue`.
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
--     `""` (empty string literal) as a clearly-wrong sentinel.  The
--     well-formedness hypothesis for a clean B.3.d roundtrip is: every
--     `AVEnum n` default has a matching AttrDef with `ATEnum labels`
--     and `n < length labels`.
module Aletheia.DBC.TextFormatter.Attributes where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; foldr)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.String using (String) renaming (_++_ to _++ₛ_)
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
  (showℕ-dec; showℤ-dec; showℚ-dec; quoteStringLit)
open import Aletheia.DBC.TextFormatter.Topology using (rawCanIdℕ)

-- ============================================================================
-- DEF LOOKUP TABLE (shared across defaults in `emitAttributes`)
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
  if ⌊ name ≟ₛ AttrDef.name d ⌋
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
-- with trailing space.  `ASNetwork` emits `""` so `BA_DEF_ "name" ...`
-- falls out naturally; the other six keywords carry their canonical DBC
-- token followed by a single space.
emitScopePrefix : AttrScope → String
emitScopePrefix ASNetwork = ""
emitScopePrefix ASNode    = "BU_ "
emitScopePrefix ASMessage = "BO_ "
emitScopePrefix ASSignal  = "SG_ "
emitScopePrefix ASEnvVar  = "EV_ "
emitScopePrefix ASNodeMsg = "BU_BO_REL_ "
emitScopePrefix ASNodeSig = "BU_SG_REL_ "

-- Relation scopes dispatch to `BA_DEF_REL_`; everything else to `BA_DEF_`.
isRelScope : AttrScope → Bool
isRelScope ASNodeMsg = true
isRelScope ASNodeSig = true
isRelScope _         = false

-- Enum labels comma-separated, each quoted.  Matches cantools output of
-- `"Low","Normal","High"` (no spaces around comma).
emitEnumLabels : List String → String
emitEnumLabels []       = ""
emitEnumLabels (x ∷ xs) =
  quoteStringLit x ++ₛ
  foldr (λ y acc → "," ++ₛ quoteStringLit y ++ₛ acc) "" xs

emitAttrType : AttrType → String
emitAttrType (ATInt mn mx)   =
  "INT "   ++ₛ showℤ-dec mn ++ₛ " " ++ₛ showℤ-dec mx
emitAttrType (ATFloat mn mx) =
  "FLOAT " ++ₛ showℚ-dec mn ++ₛ " " ++ₛ showℚ-dec mx
emitAttrType ATString        = "STRING"
emitAttrType (ATEnum labels) =
  "ENUM "  ++ₛ emitEnumLabels labels
emitAttrType (ATHex mn mx)   =
  "HEX "   ++ₛ showℕ-dec mn ++ₛ " " ++ₛ showℕ-dec mx

-- ============================================================================
-- VALUE EMITTERS
-- ============================================================================

-- Assignment context: `AVEnum n` → decimal integer (no label lookup).
emitAssignValue : AttrValue → String
emitAssignValue (AVInt z)    = showℤ-dec z
emitAssignValue (AVFloat q)  = showℚ-dec q
emitAssignValue (AVString s) = quoteStringLit s
emitAssignValue (AVEnum n)   = showℕ-dec n
emitAssignValue (AVHex n)    = showℕ-dec n

-- Default context: `AVEnum n` → look up the label at index n in the
-- matching AttrDef's ENUM labels, quoted as a string literal.  Missing
-- def, non-ENUM def, or OOB index all degrade to `""` (see module header).
emitDefaultValue : List AttrDef → (attrName : String) → AttrValue → String
emitDefaultValue _    _  (AVInt z)    = showℤ-dec z
emitDefaultValue _    _  (AVFloat q)  = showℚ-dec q
emitDefaultValue _    _  (AVString s) = quoteStringLit s
emitDefaultValue _    _  (AVHex n)    = showℕ-dec n
emitDefaultValue defs nm (AVEnum n) with lookupDef nm defs
... | nothing  = quoteStringLit ""
... | just def with AttrDef.attrType def
...   | ATEnum labels = quoteStringLit (nthLabel n labels)
...   | _             = quoteStringLit ""

-- ============================================================================
-- LINE EMITTERS
-- ============================================================================

-- `"BA_DEF_" ws (attr-scope ws)? string-lit ws attr-type ws? ";" newline`
-- vs `"BA_DEF_REL_" ws rel-scope ws string-lit ws attr-type ws? ";" newline`,
-- dispatched on scope.  Trailing ` ;\n` (space before semicolon) matches
-- the cantools BA_DEF_* convention; the shorter-line families use `;\n`
-- (no space).
emitAttrDef : AttrDef → String
emitAttrDef d with isRelScope (AttrDef.scope d)
... | true  =
  "BA_DEF_REL_ " ++ₛ emitScopePrefix (AttrDef.scope d) ++ₛ
  quoteStringLit (AttrDef.name d) ++ₛ " " ++ₛ
  emitAttrType (AttrDef.attrType d) ++ₛ " ;\n"
... | false =
  "BA_DEF_ " ++ₛ emitScopePrefix (AttrDef.scope d) ++ₛ
  quoteStringLit (AttrDef.name d) ++ₛ " " ++ₛ
  emitAttrType (AttrDef.attrType d) ++ₛ " ;\n"

-- `"BA_DEF_DEF_" ws string-lit ws attr-value ws? ";" newline`.  The
-- ambient AttrDef list flows in for ENUM label resolution.
emitAttrDefault : List AttrDef → AttrDefault → String
emitAttrDefault defs d =
  "BA_DEF_DEF_ " ++ₛ
  quoteStringLit (AttrDefault.name d) ++ₛ " " ++ₛ
  emitDefaultValue defs (AttrDefault.name d) (AttrDefault.value d) ++ₛ ";\n"

-- `"BA_" ...` vs `"BA_REL_" ...` dispatched on the target.  For each
-- target shape the explicit cases spell out the inter-token spacing
-- directly rather than routing through `emitAttrTarget`; this keeps the
-- assembly of the line simple and avoids the "target-is-network ⇒ no
-- trailing space" special case that a uniform helper would need.
emitAttrAssign : AttrAssign → String
emitAttrAssign a = body (AttrAssign.target a)
  where
    qname : String
    qname = quoteStringLit (AttrAssign.name a)
    vstr : String
    vstr = emitAssignValue (AttrAssign.value a)
    body : AttrTarget → String
    body ATgtNetwork =
      "BA_ " ++ₛ qname ++ₛ " " ++ₛ vstr ++ₛ ";\n"
    body (ATgtNode n) =
      "BA_ " ++ₛ qname ++ₛ " BU_ " ++ₛ n ++ₛ " " ++ₛ vstr ++ₛ ";\n"
    body (ATgtMessage cid) =
      "BA_ " ++ₛ qname ++ₛ " BO_ " ++ₛ showℕ-dec (rawCanIdℕ cid) ++ₛ
      " " ++ₛ vstr ++ₛ ";\n"
    body (ATgtSignal cid sig) =
      "BA_ " ++ₛ qname ++ₛ " SG_ " ++ₛ showℕ-dec (rawCanIdℕ cid) ++ₛ
      " " ++ₛ sig ++ₛ " " ++ₛ vstr ++ₛ ";\n"
    body (ATgtEnvVar ev) =
      "BA_ " ++ₛ qname ++ₛ " EV_ " ++ₛ ev ++ₛ " " ++ₛ vstr ++ₛ ";\n"
    body (ATgtNodeMsg n cid) =
      "BA_REL_ " ++ₛ qname ++ₛ " BU_BO_REL_ " ++ₛ n ++ₛ " " ++ₛ
      showℕ-dec (rawCanIdℕ cid) ++ₛ " " ++ₛ vstr ++ₛ ";\n"
    body (ATgtNodeSig n cid sig) =
      "BA_REL_ " ++ₛ qname ++ₛ " BU_SG_REL_ " ++ₛ n ++ₛ " SG_ " ++ₛ
      showℕ-dec (rawCanIdℕ cid) ++ₛ " " ++ₛ sig ++ₛ " " ++ₛ vstr ++ₛ ";\n"

-- ============================================================================
-- SECTION EMITTER
-- ============================================================================

emitAttribute : List AttrDef → DBCAttribute → String
emitAttribute _    (DBCAttrDef d)     = emitAttrDef d
emitAttribute defs (DBCAttrDefault d) = emitAttrDefault defs d
emitAttribute _    (DBCAttrAssign a)  = emitAttrAssign a

-- Precompute the def lookup table once per `emitAttributes` call and
-- thread it through the per-line fold.  Empty list emits `""` (no
-- attributes section), matching cantools behaviour on attribute-free
-- databases.  Blank-line separation between the attributes section and
-- the next section is the composer's responsibility, not this emitter's.
emitAttributes : List DBCAttribute → String
emitAttributes attrs =
  let defs = collectDefs attrs
  in foldr (λ a acc → emitAttribute defs a ++ₛ acc) "" attrs
