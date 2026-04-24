{-# OPTIONS --without-K #-}

-- Attribute parsers for the DBC text format (Phase B.3.c.5).
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
open import Aletheia.DBC.Types using (attrDefNameStr)

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Rational as Rat using (ℚ)
open import Aletheia.DBC.DecRat using (DecRat; fromℚ?)
open import Aletheia.DBC.TextParser.DecRatParse using (parseDecRat)
open import Data.Rational.Unnormalised using (mkℚᵘ)
open import Data.String using (String)
open import Data.String.Properties using () renaming (_≟_ to _≟ₛ_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Aletheia.Parser.Combinators using
  (Parser; pure; fail; _>>=_; _<|>_; _*>_; _<*_;
   char; string; many; optional)
open import Aletheia.DBC.TextParser.Lexer using
  (parseIdentifier; parseStringLit; parseWS; parseWSOpt; parseNewline;
   parseNatural; parseInt; parseRational)
open import Aletheia.DBC.TextParser.Topology using (buildCANId)

open import Aletheia.DBC.Types using
  ( AttrScope; ASNetwork; ASNode; ASMessage; ASSignal; ASEnvVar
  ; ASNodeMsg; ASNodeSig
  ; AttrType; ATInt; ATFloat; ATString; ATEnum; ATHex
  ; AttrValue; AVInt; AVFloat; AVString; AVEnum; AVHex
  ; AttrTarget; ATgtNetwork; ATgtNode; ATgtMessage; ATgtSignal
  ; ATgtEnvVar; ATgtNodeMsg; ATgtNodeSig
  ; AttrDef; mkAttrDef; AttrDefault; mkAttrDefault
  ; AttrAssign; mkAttrAssign
  ; DBCAttribute; DBCAttrDef; DBCAttrDefault; DBCAttrAssign
  )

-- ============================================================================
-- RAW WIRE FORM (pre-semantic-refinement)
-- ============================================================================

-- At parse time, all we know lexically is whether the value is a string
-- literal or a numeric literal.  Semantic refinement (INT/FLOAT/STRING/
-- ENUM/HEX disambiguation plus enum-label-lookup on defaults) happens
-- after the full attribute list is available.
data RawAttrValue : Set where
  RavString : String → RawAttrValue
  RavNumber : ℚ      → RawAttrValue

record RawAttrDefault : Set where
  constructor mkRawAttrDefault
  field
    name  : String
    value : RawAttrValue

record RawAttrAssign : Set where
  constructor mkRawAttrAssign
  field
    name   : String
    target : AttrTarget
    value  : RawAttrValue

data RawDBCAttribute : Set where
  RawDef     : AttrDef        → RawDBCAttribute
  RawDefault : RawAttrDefault → RawDBCAttribute
  RawAssign  : RawAttrAssign  → RawDBCAttribute

-- ============================================================================
-- SCOPE / TYPE LEXERS
-- ============================================================================

-- Standard scope keyword (BA_DEF_ payload when scope is non-network).
parseStandardScope : Parser AttrScope
parseStandardScope =
  (string "BU_" *> pure ASNode)    <|>
  (string "BO_" *> pure ASMessage) <|>
  (string "SG_" *> pure ASSignal)  <|>
  (string "EV_" *> pure ASEnvVar)

-- Relation scope keyword (BA_DEF_REL_ payload).
parseRelScope : Parser AttrScope
parseRelScope =
  (string "BU_BO_REL_" *> pure ASNodeMsg) <|>
  (string "BU_SG_REL_" *> pure ASNodeSig)

-- BA_DEF_ optional scope: either a standard-scope keyword followed by
-- its own `parseWS` separator, or `ASNetwork` when the scope keyword is
-- absent.  The `<*` chain ensures scope-parsed inputs consume trailing
-- whitespace so the caller can proceed straight to the attribute name.
parseOptionalStandardScope : Parser AttrScope
parseOptionalStandardScope =
  (parseStandardScope <* parseWS) <|> pure ASNetwork

parseIntType : Parser AttrType
parseIntType = do
  _ ← string "INT"
  _ ← parseWS
  mn ← parseInt
  _ ← parseWS
  mx ← parseInt
  pure (ATInt mn mx)

parseFloatType : Parser AttrType
parseFloatType = do
  _ ← string "FLOAT"
  _ ← parseWS
  mn ← parseDecRat
  _ ← parseWS
  mx ← parseDecRat
  pure (ATFloat mn mx)

parseStringType : Parser AttrType
parseStringType = string "STRING" *> pure ATString

-- Comma-separated enum labels; at least one is required by the grammar.
-- `parseWSOpt` after the comma tolerates the cantools-observed
-- `"A", "B"` and `"A","B"` forms alike.
parseEnumLabels : Parser (List String)
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
  mn ← parseNatural
  _ ← parseWS
  mx ← parseNatural
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

-- The attribute value on the wire is either a string literal or a number.
-- `parseRational` already accepts optional leading `-`, decimal fraction,
-- and scientific notation, so it covers every numeric form (int, float,
-- hex-integer-in-decimal, enum-index) emitted by cantools.
parseRawAttrValue : Parser RawAttrValue
parseRawAttrValue =
  (parseStringLit >>= λ s → pure (RavString s)) <|>
  (parseRational  >>= λ q → pure (RavNumber q))

-- ============================================================================
-- LINE PARSERS
-- ============================================================================

-- `"BA_DEF_" ws (attr-scope ws)? string-lit ws attr-type ws? ";" newline`.
-- Optional scope handled by `parseOptionalStandardScope` (backtracks to
-- `ASNetwork` when no scope keyword is present).  Each line absorbs its
-- own trailing blanks via `many parseNewline`, so `many parseAttrLine`
-- composes cleanly upstream.
parseAttrDef : Parser AttrDef
parseAttrDef = do
  _ ← string "BA_DEF_"
  _ ← parseWS
  scope ← parseOptionalStandardScope
  name  ← parseStringLit
  _ ← parseWS
  ty ← parseAttrTypeDecl
  _ ← parseWSOpt
  _ ← char ';'
  _ ← parseNewline
  _ ← many parseNewline
  pure (mkAttrDef name scope ty)

-- `"BA_DEF_REL_" ws rel-scope ws string-lit ws attr-type ws? ";" newline`.
parseAttrDefRel : Parser AttrDef
parseAttrDefRel = do
  _ ← string "BA_DEF_REL_"
  _ ← parseWS
  scope ← parseRelScope
  _ ← parseWS
  name  ← parseStringLit
  _ ← parseWS
  ty ← parseAttrTypeDecl
  _ ← parseWSOpt
  _ ← char ';'
  _ ← parseNewline
  _ ← many parseNewline
  pure (mkAttrDef name scope ty)

-- `"BA_DEF_DEF_" ws string-lit ws attr-value ws? ";" newline`.
parseRawAttrDefault : Parser RawAttrDefault
parseRawAttrDefault = do
  _ ← string "BA_DEF_DEF_"
  _ ← parseWS
  name ← parseStringLit
  _ ← parseWS
  val  ← parseRawAttrValue
  _ ← parseWSOpt
  _ ← char ';'
  _ ← parseNewline
  _ ← many parseNewline
  pure (mkRawAttrDefault name val)

-- `"BA_" ws string-lit (ws attr-target)? ws attr-value ws? ";" newline`.
-- When no target keyword follows the name, target defaults to ATgtNetwork.
-- The standard-target branch consumes its own trailing `parseWS`; the
-- network branch doesn't, so we only run the outer `parseWS` before the
-- target alternative (inside `parseStandardAttrTarget` the first token
-- is the keyword, not whitespace).
parseRawAttrAssign : Parser RawAttrAssign
parseRawAttrAssign = do
  _ ← string "BA_"
  _ ← parseWS
  name ← parseStringLit
  _ ← parseWS
  target ← parseStandardAttrTarget <|> pure ATgtNetwork
  val ← parseRawAttrValue
  _ ← parseWSOpt
  _ ← char ';'
  _ ← parseNewline
  _ ← many parseNewline
  pure (mkRawAttrAssign name target val)

-- `"BA_REL_" ws string-lit ws rel-target ws attr-value ws? ";" newline`.
parseRawAttrRel : Parser RawAttrAssign
parseRawAttrRel = do
  _ ← string "BA_REL_"
  _ ← parseWS
  name ← parseStringLit
  _ ← parseWS
  target ← parseRelTarget
  val ← parseRawAttrValue
  _ ← parseWSOpt
  _ ← char ';'
  _ ← parseNewline
  _ ← many parseNewline
  pure (mkRawAttrAssign name target val)

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

-- `ℚ` → `ℤ` coercion, succeeds iff the denominator is exactly 1.  Uses
-- `toℚᵘ` to project into the unnormalised view; `ℚ` stores values in
-- lowest terms so `denom-1 = 0` iff the value is integer-valued.
ratToInt : ℚ → Maybe ℤ
ratToInt r with Rat.toℚᵘ r
... | mkℚᵘ num zero    = just num
... | mkℚᵘ _   (suc _) = nothing

-- `ℚ` → `ℕ` coercion, succeeds iff the value is a non-negative integer.
ratToNat : ℚ → Maybe ℕ
ratToNat r with Rat.toℚᵘ r
... | mkℚᵘ (+ n)     zero    = just n
... | mkℚᵘ -[1+ _ ]  zero    = nothing
... | mkℚᵘ _         (suc _) = nothing

-- 0-based index of `s` in `labels`; `nothing` if not present.  Used by
-- `refineDefaultValue` to convert an enum-default's string label into
-- its canonical `AVEnum` index.  Enum-label uniqueness within an AttrDef
-- is a well-formedness assumption (and corpus invariant); if two labels
-- collide, `findLabel` returns the first match.
findLabel : String → List String → Maybe ℕ
findLabel _ []       = nothing
findLabel s (x ∷ xs) with ⌊ s ≟ₛ x ⌋
... | true  = just 0
... | false with findLabel s xs
...   | just n  = just (suc n)
...   | nothing = nothing

-- Refine a default value against the declared attribute type.  ENUM is
-- the odd-one-out: wire form is a label, semantic form is an index.
refineDefaultValue : AttrType → RawAttrValue → Maybe AttrValue
refineDefaultValue ATString      (RavString s) = just (AVString s)
refineDefaultValue (ATInt _ _)   (RavNumber q) with ratToInt q
... | just z  = just (AVInt z)
... | nothing = nothing
refineDefaultValue (ATFloat _ _) (RavNumber q) with fromℚ? q
... | just d  = just (AVFloat d)
... | nothing = nothing
refineDefaultValue (ATEnum ls)   (RavString s) with findLabel s ls
... | just i  = just (AVEnum i)
... | nothing = nothing
refineDefaultValue (ATHex _ _)   (RavNumber q) with ratToNat q
... | just n  = just (AVHex n)
... | nothing = nothing
refineDefaultValue _             _             = nothing

-- Refine an assignment value.  Differs from `refineDefaultValue` on the
-- ENUM branch only: wire form is the numeric index, so the conversion
-- is just `ratToNat`.
refineAssignValue : AttrType → RawAttrValue → Maybe AttrValue
refineAssignValue ATString      (RavString s) = just (AVString s)
refineAssignValue (ATInt _ _)   (RavNumber q) with ratToInt q
... | just z  = just (AVInt z)
... | nothing = nothing
refineAssignValue (ATFloat _ _) (RavNumber q) with fromℚ? q
... | just d  = just (AVFloat d)
... | nothing = nothing
refineAssignValue (ATEnum _)    (RavNumber q) with ratToNat q
... | just n  = just (AVEnum n)
... | nothing = nothing
refineAssignValue (ATHex _ _)   (RavNumber q) with ratToNat q
... | just n  = just (AVHex n)
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
-- small def counts seen in practice (corpus: single digits).
lookupDef : String → List AttrDef → Maybe AttrDef
lookupDef _ [] = nothing
lookupDef name (d ∷ rest) =
  if ⌊ name ≟ₛ attrDefNameStr d ⌋
    then just d
    else lookupDef name rest

-- Refine a single raw attribute given the ambient AttrDef list.  Defs
-- pass through untouched; defaults/assignments require a matching def
-- and a value that narrows to the declared type.
refineAttribute : List AttrDef → RawDBCAttribute → Maybe DBCAttribute
refineAttribute _    (RawDef d) = just (DBCAttrDef d)
refineAttribute defs (RawDefault (mkRawAttrDefault n rv)) with lookupDef n defs
... | nothing  = nothing
... | just def with refineDefaultValue (AttrDef.attrType def) rv
...   | just v  = just (DBCAttrDefault (mkAttrDefault n v))
...   | nothing = nothing
refineAttribute defs (RawAssign (mkRawAttrAssign n tgt rv)) with lookupDef n defs
... | nothing  = nothing
... | just def with refineAssignValue (AttrDef.attrType def) rv
...   | just v  = just (DBCAttrAssign (mkAttrAssign n tgt v))
...   | nothing = nothing

-- Walk a raw attribute list and refine each entry.  Two-pass: first
-- collect all defs, then refine against the complete def table.  Fails
-- with `nothing` if any default/assignment references an unknown
-- attribute name or supplies a value that can't be coerced to the
-- declared type.
refineAttributes : List RawDBCAttribute → Maybe (List DBCAttribute)
refineAttributes raws = refineAll (collectRawDefs raws) raws
  where
    refineAll : List AttrDef → List RawDBCAttribute → Maybe (List DBCAttribute)
    refineAll _    [] = just []
    refineAll defs (r ∷ rest) with refineAttribute defs r
    ... | nothing = nothing
    ... | just ref with refineAll defs rest
    ...   | nothing = nothing
    ...   | just rs = just (ref ∷ rs)
