-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Attribute parsers for the DBC text format.
--
-- Grammar slice covered (BNF section D from `Aletheia.DBC.TextParser`):
--   attr-def     ::= "BA_DEF_" (ws attr-scope)? ws string-lit ws attr-type
--                    ws? ";" newline
--   attr-def-rel ::= "BA_DEF_REL_" ws rel-scope ws string-lit ws attr-type
--                    ws? ";" newline
--   attr-default ::= "BA_DEF_DEF_" ws string-lit ws attr-value ws? ";" newline
--   attr-assign  ::= "BA_" ws string-lit (ws attr-target)? ws attr-value
--                    ws? ";" newline
--   attr-rel     ::= "BA_REL_" ws string-lit ws rel-target ws attr-value
--                    ws? ";" newline
--   attr-target  ::= "BU_" ws identifier | "BO_" ws nat
--                  | "SG_" ws nat ws identifier | "EV_" ws identifier
--   rel-target   ::= "BU_BO_REL_" ws identifier ws nat
--                  | "BU_SG_REL_" ws identifier ws "SG_" ws nat ws identifier
--
-- Enum-wire asymmetry (critical — not obvious from the BNF alone):
--   * `BA_DEF_DEF_` encodes enum defaults as a string-literal label, e.g.
--     `BA_DEF_DEF_  "SignalPriority" "Normal";`.  The semantic value is the
--     0-based index of `"Normal"` in the matching `AttrDef`'s ENUM labels.
--     Resolution requires a prior lookup against the AttrDefs parsed
--     earlier in the file.
--   * `BA_` / `BA_REL_` encode enum assignments as a bare numeric index,
--     e.g. `BA_ "SignalPriority" SG_ 400 Value 2;` → value 2.  No label
--     lookup is needed; the wire number IS the semantic index.
--   The two refiners (`refineDefaultValue`, `refineAssignValue`) differ
--   only in how they handle `ATEnum`: label-to-index for defaults,
--   number-to-index passthrough for assignments.
--
-- Two-stage design:
--   Stage 1 — pure combinator parse to `RawDBCAttribute` (one-per-line).
--     Preserves the wire-level string-vs-number distinction for values,
--     defers enum semantic resolution.  Combinator layer stays stateless
--     and composes under `many parseAttrLine` upstream.
--   Stage 2 — `refineAttributes` walks the raw list and resolves each
--     default/assignment against the set of AttrDefs seen in the input.
--     Uses a two-pass approach (collect defs first, then refine) so the
--     wire-order of BA_DEF_* vs BA_DEF_DEF_/BA_/BA_REL_ is not constrained.
--     Cantools emits defs before defaults-then-assignments, but hand-
--     written DBCs may interleave; the two-pass design is robust to that.
--
-- Prefix ambiguity (`BA_DEF_REL_` vs `BA_DEF_DEF_` vs `BA_DEF_` vs `BA_REL_`
-- vs `BA_`).  All five keywords share the `BA_` prefix.  The unifying
-- `parseAttrLine` uses backtracking `<|>`; ordering is immaterial for
-- correctness because the mandatory `parseWS` after each keyword
-- discriminates `BA_`-prefix from longer-keyword continuations — e.g.
-- `parseAttrAssign` on input `BA_REL_ ...` matches `string "BA_"` and then
-- fails on `parseWS` (next char `R`), backtracking cleanly.  The current
-- ordering is longest-first as a readability aid only.
module Aletheia.DBC.TextParser.Attributes where
open import Aletheia.DBC.Identifier using (Identifier)

open import Data.Bool using (true; false; if_then_else_)
open import Data.Char using (Char) renaming (_≟_ to _≟ᶜ_)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_)
import Data.List.Properties as ListProps
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Aletheia.Error using (AttrRefineCause; UnknownAttrDef; IllTypedValue)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Aletheia.DBC.DecRat using (DecRat; mkDecRat)
open import Aletheia.DBC.DecRat.Refinement using
  (IntDecRat; mkIntDecRatFromℤ; mkNatDecRatFromℕ)
open import Aletheia.DBC.TextParser.DecRatParse using
  (parseDecRat; parseIntDecRat; parseNatDecRat)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Aletheia.Parser.Combinators using
  (Parser; pure; fail; _>>=_; _<|>_; _*>_;
   char; string; many)
open import Aletheia.DBC.TextParser.Lexer using
  (parseIdentifier; parseStringLit; parseWS; parseWSOpt; parseNewline;
   parseNatural)
open import Aletheia.DBC.TextParser.Topology.Foundations using (buildCANId)

open import Aletheia.DBC.TextParser.Format using (parse)
open import Aletheia.DBC.TextParser.Format.AttrDef using
  (attrDefFmt; attrDefRelFmt; liftStdAttrDef; liftRelAttrDef)
open import Aletheia.DBC.TextParser.Format.AttrValue using
  (RawAttrValueWire; RavwString; RavwFrac; RavwBareInt)
open import Aletheia.DBC.TextParser.Format.AttrLine using
  (attrDefaultFmt; DefaultLineCarrier;
   attrAssignFmt;
   attrRelFmt;
   RawAttrTargetWire; RatwNode; RatwMsg; RatwSig; RatwEv; RatwNet;
   RawRelTargetWire; RrtNodeMsg; RrtNodeSig)

-- Re-export the cycle-relevant subset for backward source compatibility.
open import Aletheia.DBC.TextParser.Attributes.Foundations public using
  (parseStandardScope; parseRelScope; parseOptionalStandardScope;
   parseStringType)

open import Aletheia.DBC.Types using
  ( AttrType; ATInt; ATFloat; ATString; ATEnum; ATHex
  ; AttrValue; AVInt; AVFloat; AVString; AVEnum; AVHex
  ; AttrTarget; ATgtNetwork; ATgtNode; ATgtMessage; ATgtSignal
  ; ATgtEnvVar; ATgtNodeMsg; ATgtNodeSig
  ; AttrDef; mkAttrDefault
  ; mkAttrAssign
  ; DBCAttribute; DBCAttrDef; DBCAttrDefault; DBCAttrAssign
  )

-- ============================================================================
-- RAW WIRE FORM (pre-semantic-refinement)
-- ============================================================================

-- At parse time, all we know lexically is whether the value is a string
-- literal or a numeric literal.  Numeric values are normalised to
-- `DecRat` regardless of wire form (bare integer or decimal-fraction);
-- this matches the project-wide convention "all numbers are `DecRat`
-- except on the frame hot-path" (signal extraction sticks with `ℚ` for
-- performance, every other DBC numeric field is `DecRat`).
--
-- The two-way split (vs the older `RavNumber : ℚ`) keeps the substrate
-- aligned with the parsers that already have roundtrip proofs:
-- `parseStringLit-roundtrip` and `parseDecRat-roundtrip-suffix`.  Both
-- numeric wire forms (bare integer like `50` and decimal-fraction like
-- `0.5`) flow through `parseDecRat`, which subsumes the former
-- `parseInt` branch via the alt of `parseDecRatFrac <|>
-- parseDecRatBareInt` (see `Aletheia.DBC.TextParser.DecRatParse`).
-- There is no `parseRational-roundtrip` and proving it from scratch
-- (scientific notation, sign + fraction + exponent unrolling) would add
-- ~1 kLOC of foundation work for attribute proofs.
-- `RavString` and `name` carry `List Char`
-- (matching `parseStringLit : Parser (List Char)` and the AST's
-- `AttrDefault.name : List Char` / `AttrAssign.name : List Char`).
data RawAttrValue : Set where
  RavString : List Char → RawAttrValue
  RavDecRat : DecRat    → RawAttrValue

record RawAttrDefault : Set where
  constructor mkRawAttrDefault
  field
    name  : List Char
    value : RawAttrValue

record RawAttrAssign : Set where
  constructor mkRawAttrAssign
  field
    name   : List Char
    target : AttrTarget
    value  : RawAttrValue

data RawDBCAttribute : Set where
  RawDef     : AttrDef        → RawDBCAttribute
  RawDefault : RawAttrDefault → RawDBCAttribute
  RawAssign  : RawAttrAssign  → RawDBCAttribute

-- ============================================================================
-- SCOPE / TYPE LEXERS
-- ============================================================================
--
-- The four scope parsers (`parseStandardScope`, `parseRelScope`,
-- `parseOptionalStandardScope`, `parseStringType`) live in `Attributes/
-- Foundations.agda` (cycle-break for the migration; see
-- `Foundations.agda` header) and are re-exported `public` from this
-- module's import block.

parseIntType : Parser AttrType
parseIntType = do
  _ ← string "INT"
  _ ← parseWS
  mn ← parseIntDecRat
  _ ← parseWS
  mx ← parseIntDecRat
  pure (ATInt mn mx)

parseFloatType : Parser AttrType
parseFloatType = do
  _ ← string "FLOAT"
  _ ← parseWS
  mn ← parseDecRat
  _ ← parseWS
  mx ← parseDecRat
  pure (ATFloat mn mx)

-- Comma-separated enum labels; at least one is required by the grammar.
-- `parseWSOpt` after the comma tolerates the cantools-observed
-- `"A", "B"` and `"A","B"` forms alike.  Labels are `List Char` to align
-- with `ATEnum : List (List Char) → AttrType`.
parseEnumLabels : Parser (List (List Char))
parseEnumLabels = do
  h ← parseStringLit
  t ← many (char ',' *> parseWSOpt *> parseStringLit)
  pure (h ∷ t)

parseEnumType : Parser AttrType
parseEnumType = do
  _ ← string "ENUM"
  _ ← parseWS
  ls ← parseEnumLabels
  pure (ATEnum ls)

parseHexType : Parser AttrType
parseHexType = do
  _ ← string "HEX"
  _ ← parseWS
  mn ← parseNatDecRat
  _ ← parseWS
  mx ← parseNatDecRat
  pure (ATHex mn mx)

-- Attribute-type declaration (RHS of `BA_DEF_` / `BA_DEF_REL_`).  None of
-- the keywords share a prefix longer than one character so ordering is
-- purely a readability choice; here grouped by expected corpus frequency.
parseAttrTypeDecl : Parser AttrType
parseAttrTypeDecl =
  parseStringType <|>
  parseIntType    <|>
  parseFloatType  <|>
  parseEnumType   <|>
  parseHexType

-- ============================================================================
-- ATTR TARGET LEXERS
-- ============================================================================

-- CAN-ID-aware target builders.  `buildCANId` enforces the standard-vs-
-- extended range via the cantools bit-31 flag convention.  Out-of-range
-- IDs abort the parse via `fail`.
wrapMsgTarget : ℕ → Parser AttrTarget
wrapMsgTarget r with buildCANId r
... | just cid = pure (ATgtMessage cid)
... | nothing  = fail

wrapSigTarget : ℕ → Identifier → Parser AttrTarget
wrapSigTarget r sig with buildCANId r
... | just cid = pure (ATgtSignal cid sig)
... | nothing  = fail

wrapNodeMsgTarget : Identifier → ℕ → Parser AttrTarget
wrapNodeMsgTarget n r with buildCANId r
... | just cid = pure (ATgtNodeMsg n cid)
... | nothing  = fail

wrapNodeSigTarget : Identifier → ℕ → Identifier → Parser AttrTarget
wrapNodeSigTarget n r sig with buildCANId r
... | just cid = pure (ATgtNodeSig n cid sig)
... | nothing  = fail

-- Each standard-target branch consumes its trailing `parseWS` so the
-- caller can read the attribute value directly without another separator.
parseNodeTgt : Parser AttrTarget
parseNodeTgt = do
  _ ← string "BU_"
  _ ← parseWS
  n ← parseIdentifier
  _ ← parseWS
  pure (ATgtNode n)

parseMsgTgt : Parser AttrTarget
parseMsgTgt = do
  _ ← string "BO_"
  _ ← parseWS
  rawId ← parseNatural
  _ ← parseWS
  wrapMsgTarget rawId

parseSigTgt : Parser AttrTarget
parseSigTgt = do
  _ ← string "SG_"
  _ ← parseWS
  rawId ← parseNatural
  _ ← parseWS
  sig ← parseIdentifier
  _ ← parseWS
  wrapSigTarget rawId sig

parseEvTgt : Parser AttrTarget
parseEvTgt = do
  _ ← string "EV_"
  _ ← parseWS
  ev ← parseIdentifier
  _ ← parseWS
  pure (ATgtEnvVar ev)

-- Standard attr-target (non-relation).  The four keywords are lexically
-- disjoint so ordering doesn't matter.
parseStandardAttrTarget : Parser AttrTarget
parseStandardAttrTarget =
  parseNodeTgt <|>
  parseMsgTgt  <|>
  parseSigTgt  <|>
  parseEvTgt

-- Relation target.  BU_SG_REL_ carries the literal `SG_` keyword between
-- the node identifier and the (msgID, signal) pair — this is the
-- idiosyncrasy that extends `BU_BO_REL_ node msg` to `BU_SG_REL_ node SG_ msg sig`.
-- Without the `SG_` literal, the parser would not be able to tell the
-- node identifier apart from the signal identifier token-by-token.
parseNodeMsgTgt : Parser AttrTarget
parseNodeMsgTgt = do
  _ ← string "BU_BO_REL_"
  _ ← parseWS
  n ← parseIdentifier
  _ ← parseWS
  rawId ← parseNatural
  _ ← parseWS
  wrapNodeMsgTarget n rawId

parseNodeSigTgt : Parser AttrTarget
parseNodeSigTgt = do
  _ ← string "BU_SG_REL_"
  _ ← parseWS
  n ← parseIdentifier
  _ ← parseWS
  _ ← string "SG_"
  _ ← parseWS
  rawId ← parseNatural
  _ ← parseWS
  sig ← parseIdentifier
  _ ← parseWS
  wrapNodeSigTarget n rawId sig

parseRelTarget : Parser AttrTarget
parseRelTarget = parseNodeMsgTgt <|> parseNodeSigTgt

-- ============================================================================
-- RAW VALUE LEXER
-- ============================================================================

-- The attribute value on the wire is either a string literal or a
-- numeric form.  All numeric forms — decimal-fraction (`42.5`) and bare
-- integer (`50`) — go through `parseDecRat`, which internally tries
-- `parseDecRatFrac` first and falls through to `parseDecRatBareInt`.
-- Both branches yield a `DecRat`; the bare-int branch fixes the
-- denominator at 1 via `buildDecRat ... []`.  Refinement against the
-- declared `AttrType` (e.g., reject a `42.5` payload for an INT slot)
-- happens later in `refineAttributes` over `RawDBCAttribute`, not in
-- this lexer.
parseRawAttrValue : Parser RawAttrValue
parseRawAttrValue =
  (parseStringLit >>= λ s → pure (RavString s))    <|>
  (parseDecRat    >>= λ d → pure (RavDecRat d))

-- ============================================================================
-- LINE PARSERS
-- ============================================================================

-- `"BA_DEF_" ws (attr-scope ws)? string-lit ws attr-type ws? ";" newline`.
--
-- The line-portion is expressed via the
-- Format DSL (`attrDefFmt` in `Format.AttrDef`); the trailing `many
-- parseNewline` for blank-line padding stays in the production wrapper,
-- mirroring the η-style wrap of `parseEnvVar` / `parseValueTable` /
-- `parseBU`.  The previous form was a hand-written 14-step bind chain.
parseAttrDef : Parser AttrDef
parseAttrDef =
  parse attrDefFmt >>= λ result →
  many parseNewline >>= λ _ →
  pure (liftStdAttrDef result)

-- `"BA_DEF_REL_" ws rel-scope ws string-lit ws attr-type ws? ";" newline`.
parseAttrDefRel : Parser AttrDef
parseAttrDefRel =
  parse attrDefRelFmt >>= λ result →
  many parseNewline >>= λ _ →
  pure (liftRelAttrDef result)

-- Lift the 3-emit-shape wire form to the 2-ctor public `RawAttrValue`.
-- Both numeric wire ctors collapse to `RavDecRat`: `RavwFrac` carries the
-- DecRat directly (frac wire form preserves DecRat shape), `RavwBareInt`
-- carries an `IntDecRat` whose underlying DecRat is the bareInt's
-- canonical form.  Public for the per-shape dispatcher proofs in
-- `Properties/Attributes/Default.agda` (and Assign/Line follow-ups).
liftRavw : RawAttrValueWire → RawAttrValue
liftRavw (RavwString s)   = RavString s
liftRavw (RavwFrac d)     = RavDecRat d
liftRavw (RavwBareInt z)  = RavDecRat (IntDecRat.value z)

liftDefaultLine : DefaultLineCarrier → RawAttrDefault
liftDefaultLine (n , wire-val , _) = mkRawAttrDefault n (liftRavw wire-val)

-- `"BA_DEF_DEF_" ws string-lit ws attr-value ws? ";" newline`.
--
-- The line-portion is expressed via the
-- Format DSL (`attrDefaultFmt` in `Format.AttrLine`); the trailing `many
-- parseNewline` for blank-line padding stays in the production wrapper,
-- mirroring the η-style wrap of `parseAttrDef`.  The previous form was a
-- hand-written 9-step bind chain (now ≡ universal roundtrip + many
-- parseNewline + pure-lift via `liftDefaultLine`).
parseRawAttrDefault : Parser RawAttrDefault
parseRawAttrDefault =
  parse attrDefaultFmt >>= λ result →
  many parseNewline >>= λ _ →
  pure (liftDefaultLine result)

-- ============================================================================
-- WIRE → AST LIFTERS — Maybe-fail at buildCANId
-- ============================================================================
--
-- Mirror of `buildCommentP`.  Pure-target
-- cases (Network/Node/EnvVar) reduce by `pure (mkRawAttrAssign ...)`.
-- CAN-ID-bearing cases (Msg/Sig for std; both NodeMsg/NodeSig for rel)
-- use `with buildCANId`; on `nothing` (out-of-range raw ID) the parser
-- fails — matching the backtrack-then-fail behaviour of
-- `wrapMsgTarget` / `wrapSigTarget` / `wrapNodeMsgTarget` / `wrapNodeSigTarget`.

-- Maybe-form lift (used in proofs).  Definitionally equal to the
-- Parser-form `buildAttrAssignP` after pos/input projection.
liftStdTarget : RawAttrTargetWire → Maybe AttrTarget
liftStdTarget RatwNet         = just ATgtNetwork
liftStdTarget (RatwNode n)    = just (ATgtNode n)
liftStdTarget (RatwMsg r) with buildCANId r
... | just cid = just (ATgtMessage cid)
... | nothing  = nothing
liftStdTarget (RatwSig r s) with buildCANId r
... | just cid = just (ATgtSignal cid s)
... | nothing  = nothing
liftStdTarget (RatwEv ev)     = just (ATgtEnvVar ev)

liftRelTarget : RawRelTargetWire → Maybe AttrTarget
liftRelTarget (RrtNodeMsg n r) with buildCANId r
... | just cid = just (ATgtNodeMsg n cid)
... | nothing  = nothing
liftRelTarget (RrtNodeSig n r s) with buildCANId r
... | just cid = just (ATgtNodeSig n cid s)
... | nothing  = nothing

-- Parser-form lifter for BA_ assignment lines.  Plugs into the η-style
-- production wrapper after `parse attrAssignFmt >>= many parseNewline`.
buildAttrAssignP : List Char → RawAttrTargetWire → RawAttrValueWire
                 → Parser RawAttrAssign
buildAttrAssignP n RatwNet         wireVal =
  pure (mkRawAttrAssign n ATgtNetwork (liftRavw wireVal))
buildAttrAssignP n (RatwNode i)    wireVal =
  pure (mkRawAttrAssign n (ATgtNode i) (liftRavw wireVal))
buildAttrAssignP n (RatwMsg r)     wireVal with buildCANId r
... | just cid =
  pure (mkRawAttrAssign n (ATgtMessage cid) (liftRavw wireVal))
... | nothing  = fail
buildAttrAssignP n (RatwSig r s)   wireVal with buildCANId r
... | just cid =
  pure (mkRawAttrAssign n (ATgtSignal cid s) (liftRavw wireVal))
... | nothing  = fail
buildAttrAssignP n (RatwEv ev)     wireVal =
  pure (mkRawAttrAssign n (ATgtEnvVar ev) (liftRavw wireVal))

-- Parser-form lifter for BA_REL_ relation lines.
buildAttrRelP : List Char → RawRelTargetWire → RawAttrValueWire
              → Parser RawAttrAssign
buildAttrRelP n (RrtNodeMsg i r) wireVal with buildCANId r
... | just cid =
  pure (mkRawAttrAssign n (ATgtNodeMsg i cid) (liftRavw wireVal))
... | nothing  = fail
buildAttrRelP n (RrtNodeSig i r s) wireVal with buildCANId r
... | just cid =
  pure (mkRawAttrAssign n (ATgtNodeSig i cid s) (liftRavw wireVal))
... | nothing  = fail

-- `"BA_" ws string-lit (ws attr-target)? ws attr-value ws? ";" newline`.
--
-- The line-portion is expressed via the
-- Format DSL (`attrAssignFmt` in `Format.AttrLine`); the trailing `many
-- parseNewline` for blank-line padding stays in the production wrapper,
-- mirroring the η-style wrap of `parseAttrDef` / `parseRawAttrDefault`.
-- Maybe-fail at buildCANId is handled inside `buildAttrAssignP`.
parseRawAttrAssign : Parser RawAttrAssign
parseRawAttrAssign =
  parse attrAssignFmt >>= λ result →
  many parseNewline >>= λ _ →
  buildAttrAssignP (proj₁ result)
                   (proj₁ (proj₂ result))
                   (proj₁ (proj₂ (proj₂ result)))

-- `"BA_REL_" ws string-lit ws rel-target ws attr-value ws? ";" newline`.
parseRawAttrRel : Parser RawAttrAssign
parseRawAttrRel =
  parse attrRelFmt >>= λ result →
  many parseNewline >>= λ _ →
  buildAttrRelP (proj₁ result)
                (proj₁ (proj₂ result))
                (proj₁ (proj₂ (proj₂ result)))

-- One attribute line.  Longest-keyword-first is a readability choice; the
-- post-keyword `parseWS` handles the actual prefix disambiguation (see
-- module header note).
parseAttrLine : Parser RawDBCAttribute
parseAttrLine =
  (parseAttrDefRel     >>= λ d → pure (RawDef d))     <|>
  (parseRawAttrDefault >>= λ d → pure (RawDefault d)) <|>
  (parseAttrDef        >>= λ d → pure (RawDef d))     <|>
  (parseRawAttrRel     >>= λ a → pure (RawAssign a))  <|>
  (parseRawAttrAssign  >>= λ a → pure (RawAssign a))

-- ============================================================================
-- REFINEMENT (stage 2 — enum label lookup + type-dispatched narrowing)
-- ============================================================================

-- `DecRat` → `ℤ` coercion, succeeds iff the value is integer-valued
-- (`twoExp = 0` and `fiveExp = 0` together imply the denominator
-- `2^a · 5^b = 1`).  The canonical-form invariant on `DecRat` makes this
-- check structural — no gcd, no normalisation.
decRatToℤ? : DecRat → Maybe ℤ
decRatToℤ? (mkDecRat z zero    zero    _) = just z
decRatToℤ? (mkDecRat _ (suc _) _       _) = nothing
decRatToℤ? (mkDecRat _ _       (suc _) _) = nothing

-- `DecRat` → `ℕ` coercion: integer-valued AND non-negative.
decRatToℕ? : DecRat → Maybe ℕ
decRatToℕ? (mkDecRat (+ n)     zero    zero    _) = just n
decRatToℕ? (mkDecRat -[1+ _ ]  zero    zero    _) = nothing
decRatToℕ? (mkDecRat _         (suc _) _       _) = nothing
decRatToℕ? (mkDecRat _         _       (suc _) _) = nothing

-- 0-based index of `s` in `labels`; `nothing` if not present.  Used by
-- `refineDefaultValue` to convert an enum-default's string label into
-- its canonical `AVEnum` index.  Enum-label uniqueness within an AttrDef
-- is a well-formedness assumption (and corpus invariant); if two labels
-- collide, `findLabel` returns the first match.  `List Char` to align with `ATEnum : List (List Char) → AttrType`.
findLabel : List Char → List (List Char) → Maybe ℕ
findLabel _ []       = nothing
findLabel s (x ∷ xs) with ⌊ ListProps.≡-dec _≟ᶜ_ s x ⌋
... | true  = just 0
... | false with findLabel s xs
...   | just n  = just (suc n)
...   | nothing = nothing

-- Refine a default value against the declared attribute type.  ENUM is
-- the odd-one-out: wire form is a label, semantic form is an index.
-- Numeric coercions go through `mkIntDecRatFromℤ` / `mkNatDecRatFromℕ`
-- to recover the refinement-type witness from the structurally-projected
-- integer.
refineDefaultValue : AttrType → RawAttrValue → Maybe AttrValue
refineDefaultValue ATString      (RavString s) = just (AVString s)
refineDefaultValue (ATInt _ _)   (RavDecRat d) with decRatToℤ? d
... | just z  = just (AVInt (mkIntDecRatFromℤ z))
... | nothing = nothing
refineDefaultValue (ATFloat _ _) (RavDecRat d) = just (AVFloat d)
refineDefaultValue (ATEnum ls)   (RavString s) with findLabel s ls
... | just i  = just (AVEnum (mkNatDecRatFromℕ i))
... | nothing = nothing
refineDefaultValue (ATHex _ _)   (RavDecRat d) with decRatToℕ? d
... | just n  = just (AVHex (mkNatDecRatFromℕ n))
... | nothing = nothing
refineDefaultValue _             _             = nothing

-- Refine an assignment value.  Differs from `refineDefaultValue` on the
-- ENUM branch only: assignments encode the index as a bare integer, so
-- the conversion is just `decRatToℕ?` (the wire form is normalised to
-- `RavDecRat` via `fromℤ`, so the denominator structure is `2^0 · 5^0 = 1`).
refineAssignValue : AttrType → RawAttrValue → Maybe AttrValue
refineAssignValue ATString      (RavString s) = just (AVString s)
refineAssignValue (ATInt _ _)   (RavDecRat d) with decRatToℤ? d
... | just z  = just (AVInt (mkIntDecRatFromℤ z))
... | nothing = nothing
refineAssignValue (ATFloat _ _) (RavDecRat d) = just (AVFloat d)
refineAssignValue (ATEnum _)    (RavDecRat d) with decRatToℕ? d
... | just n  = just (AVEnum (mkNatDecRatFromℕ n))
... | nothing = nothing
refineAssignValue (ATHex _ _)   (RavDecRat d) with decRatToℕ? d
... | just n  = just (AVHex (mkNatDecRatFromℕ n))
... | nothing = nothing
refineAssignValue _             _             = nothing

-- Collect every AttrDef from a raw attribute list, preserving wire order.
-- Used by `refineAttributes` to establish the name → AttrType lookup
-- before the per-attribute refinement pass.
collectRawDefs : List RawDBCAttribute → List AttrDef
collectRawDefs [] = []
collectRawDefs (RawDef d     ∷ rest) = d ∷ collectRawDefs rest
collectRawDefs (RawDefault _ ∷ rest) = collectRawDefs rest
collectRawDefs (RawAssign _  ∷ rest) = collectRawDefs rest

-- Look up an attribute definition by name.  Linear scan; fine for the
-- small def counts seen in practice (corpus: single digits).  Both name and
-- AttrDef.name are `List Char`.
lookupDef : List Char → List AttrDef → Maybe AttrDef
lookupDef _ [] = nothing
lookupDef name (d ∷ rest) =
  if ⌊ ListProps.≡-dec _≟ᶜ_ name (AttrDef.name d) ⌋
    then just d
    else lookupDef name rest

-- Refine a single raw attribute given the ambient AttrDef list.  Defs
-- pass through untouched; defaults/assignments require a matching def
-- and a value that narrows to the declared type.
refineAttribute : List AttrDef → RawDBCAttribute → AttrRefineCause ⊎ DBCAttribute
refineAttribute _    (RawDef d) = inj₂ (DBCAttrDef d)
refineAttribute defs (RawDefault (mkRawAttrDefault n rv)) with lookupDef n defs
... | nothing  = inj₁ UnknownAttrDef
... | just def with refineDefaultValue (AttrDef.attrType def) rv
...   | just v  = inj₂ (DBCAttrDefault (mkAttrDefault n v))
...   | nothing = inj₁ IllTypedValue
refineAttribute defs (RawAssign (mkRawAttrAssign n tgt rv)) with lookupDef n defs
... | nothing  = inj₁ UnknownAttrDef
... | just def with refineAssignValue (AttrDef.attrType def) rv
...   | just v  = inj₂ (DBCAttrAssign (mkAttrAssign n tgt v))
...   | nothing = inj₁ IllTypedValue

-- Inner refinement walk over a precomputed AttrDef table.  Lifted from
-- `refineAttributes`'s where-block so Layer-4c proofs (under
-- `Properties.Aggregator.Refine`) can reason about `refineAll defs xs`
-- with `defs` ≢ `collectRawDefs xs` — the WF-bridged path uses
-- `defs = collectDefs (typed-attrs)` while the input is the rawified
-- typed list.
-- The attribute name a raw entry declares — reported on refinement
-- failure so the error pinpoints WHICH `BA_DEF_` / `BA_DEF_DEF_` / `BA_`
-- line is at fault.
rawAttrName : RawDBCAttribute → List Char
rawAttrName (RawDef d)     = AttrDef.name d
rawAttrName (RawDefault d) = RawAttrDefault.name d
rawAttrName (RawAssign a)  = RawAttrAssign.name a

refineAll : List AttrDef → List RawDBCAttribute
          → (AttrRefineCause × List Char) ⊎ List DBCAttribute
refineAll _    [] = inj₂ []
refineAll defs (r ∷ rest) with refineAttribute defs r
... | inj₁ cause = inj₁ (cause , rawAttrName r)
... | inj₂ ref with refineAll defs rest
...   | inj₁ bad = inj₁ bad
...   | inj₂ rs  = inj₂ (ref ∷ rs)

-- Walk a raw attribute list and refine each entry.  Two-pass: first
-- collect all defs, then refine against the complete def table.  Fails
-- with `inj₁ (cause , name)` — WHY the entry was rejected (unknown
-- attribute vs ill-typed value) and WHICH attribute it names.
refineAttributes : List RawDBCAttribute
                 → (AttrRefineCause × List Char) ⊎ List DBCAttribute
refineAttributes raws = refineAll (collectRawDefs raws) raws
