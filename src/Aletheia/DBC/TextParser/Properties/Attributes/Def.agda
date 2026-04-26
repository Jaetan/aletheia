{-# OPTIONS --without-K #-}

-- B.3.d Layer 3 Commit 3c.1 — `parseAttrDef` + `parseAttrDefRel`
-- per-line-construct roundtrips.
--
-- Two parsers + two formatter dispatches keyed on `isRelScope`:
--   * `parseAttrDef` consumes `"BA_DEF_" ws (scope ws)? string-lit ws
--     attr-type ws? ";" newline (many newline)`.
--   * `parseAttrDefRel` consumes `"BA_DEF_REL_" ws rel-scope ws string-
--     lit ws attr-type ws? ";" newline (many newline)`.
--
-- The formatter `emitAttrDef-chars` dispatches on `isRelScope (AttrDef.
-- scope d)` and emits the matching shape (with or without the
-- standard `BA_DEF_REL_` prefix and rel-scope payload).  The roundtrip
-- proofs accordingly take an `isRelScope` discriminator as a
-- precondition to align parser and formatter dispatch.

module Aletheia.DBC.TextParser.Properties.Attributes.Def where

open import Data.Bool using (Bool; true; false; T)
open import Data.Char using (Char)
open import Data.Char.Base using (_≈ᵇ_; isDigit)
open import Data.List using (List; []; _∷_; length) renaming (_++_ to _++ₗ_)
open import Data.List.Properties using () renaming (++-assoc to ++ₗ-assoc; length-++ to length-++ₗ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃₂; _,_; Σ; _×_)
open import Data.String using (String; toList)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; _≢_)

open import Aletheia.Parser.Combinators
  using (Position; Parser; ParseResult; mkResult; advancePosition; advancePositions;
         _>>=_; pure; _<|>_; _*>_; _<*_; string;
         char; many)
open import Aletheia.DBC.Types using
  ( AttrType; ATInt; ATFloat; ATString; ATEnum; ATHex
  ; AttrScope; ASNetwork; ASNode; ASMessage; ASSignal; ASEnvVar
  ; ASNodeMsg; ASNodeSig
  ; AttrDef; mkAttrDef; attrDefNameStr)
open import Aletheia.DBC.Identifier using (Identifier)

open import Aletheia.DBC.TextParser.Attributes
  using (parseAttrDef; parseAttrDefRel;
         parseAttrTypeDecl; parseStandardScope;
         parseRelScope; parseOptionalStandardScope)
open import Aletheia.DBC.TextParser.Lexer
  using (parseWS; parseWSOpt; parseStringLit; parseNewline; isHSpace)

open import Aletheia.DBC.TextFormatter.Attributes
  using (emitAttrDef-chars; emitAttrType-chars; emitScopePrefix-chars;
         isRelScope)
open import Aletheia.DBC.TextFormatter.Emitter using (quoteStringLit-chars)

open import Aletheia.DBC.TextParser.Properties.Primitives using
  ( parseWS-one-space; parseStringLit-roundtrip
  ; parseOptionalStandardScope-ASNode-roundtrip
  ; parseOptionalStandardScope-ASMessage-roundtrip
  ; parseOptionalStandardScope-ASSignal-roundtrip
  ; parseOptionalStandardScope-ASEnvVar-roundtrip
  ; parseOptionalStandardScope-ASNetwork-roundtrip
  ; parseRelScopeWS; parseRelScopeWS-ASNodeMsg-roundtrip
  ; parseRelScopeWS-ASNodeSig-roundtrip
  ; alt-right-nothing; alt-left-just; bind-nothing
  ; string-success; string-*>-success)
open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  ( bind-just-step
  ; SuffixStops; ∷-stop; []-stop
  ; advancePositions-++
  ; manyHelper-satisfy-exhaust-many)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  ( isNewlineStart
  ; parseNewline-match-LF
  ; manyHelper-parseNewline-exhaust)

open import Aletheia.DBC.TextParser.Properties.Attributes.Type using
  ( parseAttrTypeDecl-roundtrip-ATString
  ; parseAttrTypeDecl-roundtrip-ATInt
  ; parseAttrTypeDecl-roundtrip-ATFloat
  ; parseAttrTypeDecl-roundtrip-ATEnum
  ; parseAttrTypeDecl-roundtrip-ATHex)

-- ============================================================================
-- Well-formedness for `AttrDef`
-- ============================================================================
--
-- `parseAttrDef` requires:
--   * The scope is a standard scope (not rel).  `parseAttrDefRel` flips
--     this requirement.
--   * The name's first char is `'"'` (well-formed for parseStringLit).
--   * If the type is `ATEnum xs`, then `xs ≡ y ∷ ys` (non-empty).
--
-- Captured as a `WfAttrDef-NotRel` / `WfAttrDef-Rel` predicate.

data WfAttrType : AttrType → Set where
  WfATInt    : ∀ mn mx → WfAttrType (ATInt mn mx)
  WfATFloat  : ∀ mn mx → WfAttrType (ATFloat mn mx)
  WfATString : WfAttrType ATString
  WfATEnum   : ∀ x xs → WfAttrType (ATEnum (x ∷ xs))
  WfATHex    : ∀ mn mx → WfAttrType (ATHex mn mx)

-- ============================================================================
-- Per-attr-type bridge: `parseAttrTypeDecl-roundtrip` over WfAttrType
-- ============================================================================
--
-- All `parseAttrTypeDecl-roundtrip-AT*` lemmas have signature
-- `∀ ... pos suffix → preconditions → parseAttrTypeDecl pos
-- (emitAttrType-chars ty ++ suffix) ≡ just ...`.  The preconditions
-- vary per case.  In our use site (parseAttrDef's bind chain) suffix
-- is `' ' ∷ ';' ∷ '\n' ∷ outer-suffix`, whose head `' '` satisfies
-- *all* SuffixStops conditions.  Bridge once here.

private
  attrType-suffix-stops-isDigit :
    ∀ (rest : List Char) → SuffixStops isDigit (' ' ∷ rest)
  attrType-suffix-stops-isDigit _ = ∷-stop refl

  attrType-suffix-not-dot :
    ∀ (rest : List Char)
    → '.' ≢ Aletheia.DBC.TextParser.DecRatParse.Properties.headOr (' ' ∷ rest) '_'
  attrType-suffix-not-dot _ = λ ()

  attrType-suffix-stops-quote :
    ∀ (rest : List Char) → SuffixStops (λ c → c ≈ᵇ '"') (' ' ∷ rest)
  attrType-suffix-stops-quote _ = ∷-stop refl

  attrType-suffix-stops-comma :
    ∀ (rest : List Char) → SuffixStops (λ c → c ≈ᵇ ',') (' ' ∷ rest)
  attrType-suffix-stops-comma _ = ∷-stop refl

-- One-shot dispatch: pattern-match on `WfAttrType` to call the
-- matching per-tag roundtrip.  Suffix is `' ' ∷ rest`.
parseAttrTypeDecl-roundtrip : ∀ {ty} pos (rest : List Char)
  → WfAttrType ty
  → parseAttrTypeDecl pos (emitAttrType-chars ty ++ₗ ' ' ∷ rest)
    ≡ just (mkResult ty
              (advancePositions pos (emitAttrType-chars ty))
              (' ' ∷ rest))
parseAttrTypeDecl-roundtrip pos rest WfATString =
  parseAttrTypeDecl-roundtrip-ATString pos (' ' ∷ rest)
parseAttrTypeDecl-roundtrip pos rest (WfATInt mn mx) =
  parseAttrTypeDecl-roundtrip-ATInt mn mx pos (' ' ∷ rest)
    (attrType-suffix-stops-isDigit rest)
    (attrType-suffix-not-dot rest)
parseAttrTypeDecl-roundtrip pos rest (WfATFloat mn mx) =
  parseAttrTypeDecl-roundtrip-ATFloat mn mx pos (' ' ∷ rest)
    (attrType-suffix-stops-isDigit rest)
parseAttrTypeDecl-roundtrip pos rest (WfATEnum x xs) =
  parseAttrTypeDecl-roundtrip-ATEnum x xs pos (' ' ∷ rest)
    (attrType-suffix-stops-quote rest)
    (attrType-suffix-stops-comma rest)
parseAttrTypeDecl-roundtrip pos rest (WfATHex mn mx) =
  parseAttrTypeDecl-roundtrip-ATHex mn mx pos (' ' ∷ rest)
    (attrType-suffix-stops-isDigit rest)
    (attrType-suffix-not-dot rest)

-- ============================================================================
-- parseAttrDef-roundtrip — `BA_DEF_` per-line construct
-- ============================================================================
--
-- `parseAttrDef` is the standard-scope (`isRelScope ≡ false`) variant.
-- Pattern-match on `AttrDef.scope d` to dispatch on the scope-prefix
-- formatter shape (`""`, `"BU_ "`, `"BO_ "`, `"SG_ "`, `"EV_ "`).  The
-- rel-scope cases (`ASNodeMsg`, `ASNodeSig`) are excluded by
-- `WfAttrDef-NotRel`.

-- Witness that `AttrDef.scope d` is a standard scope (not rel).
data WfAttrDef-NotRel : AttrDef → Set where
  Wf-Network : ∀ {n ty} → WfAttrType ty → WfAttrDef-NotRel (mkAttrDef n ASNetwork ty)
  Wf-Node    : ∀ {n ty} → WfAttrType ty → WfAttrDef-NotRel (mkAttrDef n ASNode    ty)
  Wf-Message : ∀ {n ty} → WfAttrType ty → WfAttrDef-NotRel (mkAttrDef n ASMessage ty)
  Wf-Signal  : ∀ {n ty} → WfAttrType ty → WfAttrDef-NotRel (mkAttrDef n ASSignal  ty)
  Wf-EnvVar  : ∀ {n ty} → WfAttrType ty → WfAttrDef-NotRel (mkAttrDef n ASEnvVar  ty)

-- Helper: the parseAttrDef bind chain after `string "BA_DEF_"`.
-- Encapsulates the rest as a continuation parameterised by scope.
private
  attrDef-cont : (scope : AttrScope) → AttrType → String → Parser AttrDef
  attrDef-cont scope _ _ =
    parseWS >>= λ _ →
    parseOptionalStandardScope >>= λ s →
    parseStringLit >>= λ name →
    parseWS >>= λ _ →
    parseAttrTypeDecl >>= λ ty →
    parseWSOpt >>= λ _ →
    char ';' >>= λ _ →
    parseNewline >>= λ _ →
    many parseNewline >>= λ _ →
    pure (mkAttrDef name s ty)

-- Concrete scope-prefix chars for each non-Network case.
private
  scope-chars-of : AttrScope → List Char
  scope-chars-of = emitScopePrefix-chars

-- For each scope, the post-string "BA_DEF_" position.
postKeyword-pos : Position → Position
postKeyword-pos pos = advancePositions pos (toList "BA_DEF_")

-- ============================================================================
-- The bind-chain step structure for parseAttrDef
-- ============================================================================
--
-- Given a fixed scope-AttrType-name shape, the proof composes 9
-- bind-just-step calls plus the final pure.  Each step uses the
-- corresponding primitive's roundtrip lemma.
--
-- We isolate the scope-dependent step (parseOptionalStandardScope) into
-- a helper `scope-step-eq` that returns the inputshape and position
-- trace for each scope case.  All other steps are scope-independent.

private
  -- Position trace shared across scope cases.  Parameterised by scope-
  -- specific position after parseOptionalStandardScope.
  module Trace (pos : Position) (scope : AttrScope)
               (name : String) (ty : AttrType)
               (outer-suffix : List Char) where
    cs-scope = emitScopePrefix-chars scope
    cs-name  = quoteStringLit-chars name
    cs-type  = emitAttrType-chars ty
    cs-tail  = toList " ;\n"

    pos1 : Position
    pos1 = advancePositions pos (toList "BA_DEF_")

    pos2 : Position
    pos2 = advancePosition pos1 ' '

    pos3 : Position
    pos3 = advancePositions pos2 cs-scope

    pos4 : Position
    pos4 = advancePositions pos3 cs-name

    pos5 : Position
    pos5 = advancePosition pos4 ' '

    pos6 : Position
    pos6 = advancePositions pos5 cs-type

    pos7 : Position  -- after parseWSOpt
    pos7 = advancePosition pos6 ' '

    pos8 : Position  -- after char ';'
    pos8 = advancePosition pos7 ';'

    pos9 : Position  -- after parseNewline
    pos9 = advancePosition pos8 '\n'

    -- Input slices.
    rest-tail : List Char
    rest-tail = ' ' ∷ ';' ∷ '\n' ∷ outer-suffix

    body-after-keyword : List Char
    body-after-keyword =
      ' ' ∷ cs-scope ++ₗ cs-name ++ₗ ' ' ∷ cs-type ++ₗ rest-tail

    body-after-WS1 : List Char
    body-after-WS1 = cs-scope ++ₗ cs-name ++ₗ ' ' ∷ cs-type ++ₗ rest-tail

    body-after-scope : List Char
    body-after-scope = cs-name ++ₗ ' ' ∷ cs-type ++ₗ rest-tail

    body-after-name : List Char
    body-after-name = ' ' ∷ cs-type ++ₗ rest-tail

    body-after-WS3 : List Char
    body-after-WS3 = cs-type ++ₗ rest-tail

    body-after-type : List Char
    body-after-type = rest-tail

    body-after-WSOpt : List Char
    body-after-WSOpt = ';' ∷ '\n' ∷ outer-suffix

    body-after-semi : List Char
    body-after-semi = '\n' ∷ outer-suffix

    body-after-NL : List Char
    body-after-NL = outer-suffix


-- ============================================================================
-- parseAttrDef-roundtrip — main proof
-- ============================================================================

-- Parameterised inner lemma: given a `parseOptionalStandardScope pos2
-- input ≡ just (mkResult scope pos3 input')` witness, the rest of the
-- bind chain composes uniformly.  Each scope case discharges the
-- witness with its own primitive (parseOptionalStandardScope-AS*-roundtrip).
parseAttrDef-after-keyword :
  ∀ pos (scope : AttrScope) (name : String) (ty : AttrType)
    (outer-suffix : List Char)
  → WfAttrType ty
  → SuffixStops isNewlineStart outer-suffix
  → let open Trace pos scope name ty outer-suffix in
    parseOptionalStandardScope pos2 body-after-WS1
      ≡ just (mkResult scope pos3 body-after-scope)
  → parseAttrDef pos
      ('B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷
        Trace.body-after-keyword pos scope name ty outer-suffix)
    ≡ just (mkResult (mkAttrDef name scope ty)
              (Trace.pos9 pos scope name ty outer-suffix)
              outer-suffix)
parseAttrDef-after-keyword pos scope name ty outer-suffix wf-ty ss-NL scope-eq =
    -- Step 1: string "BA_DEF_"
    trans (bind-just-step (string "BA_DEF_")
           (λ _ → parseWS >>= λ _ →
                  parseOptionalStandardScope >>= λ s →
                  parseStringLit >>= λ n →
                  parseWS >>= λ _ →
                  parseAttrTypeDecl >>= λ ty₁ →
                  parseWSOpt >>= λ _ →
                  char ';' >>= λ _ →
                  parseNewline >>= λ _ →
                  many parseNewline >>= λ _ →
                  pure (mkAttrDef n s ty₁))
           pos
           ('B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ body-after-keyword)
           "BA_DEF_" pos1 body-after-keyword
           (string-success pos "BA_DEF_" body-after-keyword))
    -- Step 2: parseWS consumes ' '.
    (trans (bind-just-step parseWS
              (λ _ → parseOptionalStandardScope >>= λ s →
                     parseStringLit >>= λ n →
                     parseWS >>= λ _ →
                     parseAttrTypeDecl >>= λ ty₁ →
                     parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkAttrDef n s ty₁))
              pos1 body-after-keyword
              (' ' ∷ []) pos2 body-after-WS1
              (parseWS-one-space pos1 body-after-WS1
                (scope-prefix-stops-isHSpace scope name body-after-name)))
    -- Step 3: parseOptionalStandardScope (scope-eq witness).
    (trans (bind-just-step parseOptionalStandardScope
              (λ s → parseStringLit >>= λ n →
                     parseWS >>= λ _ →
                     parseAttrTypeDecl >>= λ ty₁ →
                     parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkAttrDef n s ty₁))
              pos2 body-after-WS1
              scope pos3 body-after-scope
              scope-eq)
    -- Step 4: parseStringLit reads name.
    (trans (bind-just-step parseStringLit
              (λ n → parseWS >>= λ _ →
                     parseAttrTypeDecl >>= λ ty₁ →
                     parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkAttrDef n scope ty₁))
              pos3 body-after-scope
              name pos4 body-after-name
              (parseStringLit-roundtrip pos3 name body-after-name name-suffix-quote-stops))
    -- Step 5: parseWS consumes ' '.
    (trans (bind-just-step parseWS
              (λ _ → parseAttrTypeDecl >>= λ ty₁ →
                     parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkAttrDef name scope ty₁))
              pos4 body-after-name
              (' ' ∷ []) pos5 body-after-WS3
              (parseWS-one-space pos4 body-after-WS3
                (attrType-emit-stops-isHSpace ty rest-tail)))
    -- Step 6: parseAttrTypeDecl reads ty.
    (trans (bind-just-step parseAttrTypeDecl
              (λ ty₁ → parseWSOpt >>= λ _ →
                       char ';' >>= λ _ →
                       parseNewline >>= λ _ →
                       many parseNewline >>= λ _ →
                       pure (mkAttrDef name scope ty₁))
              pos5 body-after-WS3
              ty pos6 body-after-type
              (parseAttrTypeDecl-roundtrip pos5 (';' ∷ '\n' ∷ outer-suffix) wf-ty))
    -- Step 7: parseWSOpt consumes ' '.
    (trans (bind-just-step parseWSOpt
              (λ _ → char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkAttrDef name scope ty))
              pos6 body-after-type
              (' ' ∷ []) pos7 body-after-WSOpt
              (parseWSOpt-step pos6 outer-suffix))
    -- Step 8: char ';' consumes ';'.
    (trans (bind-just-step (char ';')
              (λ _ → parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkAttrDef name scope ty))
              pos7 body-after-WSOpt
              ';' pos8 body-after-semi
              refl)
    -- Step 9: parseNewline consumes '\n'.
    (trans (bind-just-step parseNewline
              (λ _ → many parseNewline >>= λ _ →
                     pure (mkAttrDef name scope ty))
              pos8 body-after-semi
              '\n' pos9 body-after-NL
              (parseNewline-match-LF pos8 outer-suffix))
    -- Step 10: many parseNewline consumes 0 newlines.
    (trans (bind-just-step (many parseNewline)
              (λ _ → pure (mkAttrDef name scope ty))
              pos9 body-after-NL
              [] pos9 outer-suffix
              (manyHelper-parseNewline-exhaust pos9 outer-suffix
                (length outer-suffix) ss-NL))
      refl)))))))))
  where
    open Trace pos scope name ty outer-suffix

    -- After parseWS consumes the trailing space of "BA_DEF_ ", the
    -- input is `cs-scope ++ cs-name ++ ...`.  Its head depends on
    -- `cs-scope` (or, for ASNetwork = empty, `cs-name`'s head = `'"'`).
    -- We need `SuffixStops isHSpace body-after-WS1`.  In all 5 cases:
    --   ASNetwork: head is `'"'` (start of cs-name).
    --   ASNode/...: head is the scope keyword's first char (B/B/S/E),
    --   which is non-hspace.
    scope-prefix-stops-isHSpace : ∀ (scp : AttrScope) (s : String) (cs-rest : List Char)
      → SuffixStops isHSpace (emitScopePrefix-chars scp ++ₗ quoteStringLit-chars s ++ₗ cs-rest)
    scope-prefix-stops-isHSpace ASNetwork  _ _ = ∷-stop refl
    scope-prefix-stops-isHSpace ASNode     _ _ = ∷-stop refl
    scope-prefix-stops-isHSpace ASMessage  _ _ = ∷-stop refl
    scope-prefix-stops-isHSpace ASSignal   _ _ = ∷-stop refl
    scope-prefix-stops-isHSpace ASEnvVar   _ _ = ∷-stop refl
    scope-prefix-stops-isHSpace ASNodeMsg  _ _ = ∷-stop refl
    scope-prefix-stops-isHSpace ASNodeSig  _ _ = ∷-stop refl

    name-suffix-quote-stops :
      SuffixStops (λ c → c ≈ᵇ '"') body-after-name
    name-suffix-quote-stops = ∷-stop refl

    attrType-emit-stops-isHSpace :
      ∀ (ty₁ : AttrType) (rest : List Char)
      → SuffixStops isHSpace (emitAttrType-chars ty₁ ++ₗ rest)
    attrType-emit-stops-isHSpace (ATInt _ _)   _ = ∷-stop refl
    attrType-emit-stops-isHSpace (ATFloat _ _) _ = ∷-stop refl
    attrType-emit-stops-isHSpace ATString      _ = ∷-stop refl
    attrType-emit-stops-isHSpace (ATEnum _)    _ = ∷-stop refl
    attrType-emit-stops-isHSpace (ATHex _ _)   _ = ∷-stop refl

    parseWSOpt-step :
      ∀ (p : Position) (rest : List Char) →
      parseWSOpt p (' ' ∷ ';' ∷ '\n' ∷ rest)
      ≡ just (mkResult (' ' ∷ [])
              (advancePosition p ' ')
              (';' ∷ '\n' ∷ rest))
    parseWSOpt-step p rest =
      manyHelper-satisfy-exhaust-many isHSpace
        p (' ' ∷ []) (';' ∷ '\n' ∷ rest)
        (refl AllList.∷ AllList.[])
        (∷-stop refl)
      where
        import Data.List.Relation.Unary.All as AllList

-- ============================================================================
-- parseAttrDef-roundtrip — top-level dispatcher
-- ============================================================================

-- Helper: shape `emitAttrDef-chars d` when scope is not rel.  Pattern-
-- matches on the scope argument concretely; this side-steps the
-- `with isRelScope ...` clause that doesn't reduce on `mkAttrDef _ _ _`
-- with abstract scope (per `feedback_expose_scrutinee_for_external_rewrite`).
emitAttrDef-NotRel-shape : ∀ (name : String) (scope : AttrScope) (ty : AttrType)
  → isRelScope scope ≡ false
  → emitAttrDef-chars (mkAttrDef name scope ty)
    ≡ toList "BA_DEF_ " ++ₗ emitScopePrefix-chars scope ++ₗ
      quoteStringLit-chars name ++ₗ
      ' ' ∷ emitAttrType-chars ty ++ₗ toList " ;\n"
emitAttrDef-NotRel-shape name ASNetwork ty refl = refl
emitAttrDef-NotRel-shape name ASNode    ty refl = refl
emitAttrDef-NotRel-shape name ASMessage ty refl = refl
emitAttrDef-NotRel-shape name ASSignal  ty refl = refl
emitAttrDef-NotRel-shape name ASEnvVar  ty refl = refl
emitAttrDef-NotRel-shape _    ASNodeMsg _  ()
emitAttrDef-NotRel-shape _    ASNodeSig _  ()

-- Discharge the scope-specific input/position witness for each of the
-- 5 standard scopes.
private
  -- For non-Network scopes: parseOptionalStandardScope succeeds via
  -- the matching primitive (ASNode / ASMessage / ASSignal / ASEnvVar).
  -- The post-scope input is `quoteStringLit-chars name ++ rest`.
  scope-stops-quote : ∀ (s : String) (cs-rest : List Char)
    → SuffixStops isHSpace (quoteStringLit-chars s ++ₗ cs-rest)
  scope-stops-quote _ _ = ∷-stop refl

  -- Discharge `parseStandardScope pos suffix ≡ nothing` for the
  -- ASNetwork case: suffix's head is `'"'` (start of the quoted name),
  -- which is not any of `B`, `S`, `E` (the parseStandardScope keywords).
  parseStandardScope-fail-on-quote : ∀ pos s rest →
    parseStandardScope pos (quoteStringLit-chars s ++ₗ rest) ≡ nothing
  parseStandardScope-fail-on-quote pos s rest = refl

-- The main proof.  Pattern-match on `WfAttrDef-NotRel` to resolve
-- scope, then call `parseAttrDef-after-keyword` with the matching
-- primitive's roundtrip lemma.

parseAttrDef-roundtrip : ∀ (d : AttrDef) (pos : Position) (outer-suffix : List Char)
  → WfAttrDef-NotRel d
  → SuffixStops isNewlineStart outer-suffix
  → parseAttrDef pos (emitAttrDef-chars d ++ₗ outer-suffix)
    ≡ just (mkResult d
              (advancePositions pos (emitAttrDef-chars d))
              outer-suffix)
parseAttrDef-roundtrip
  (mkAttrDef name ASNetwork ty) pos outer-suffix (Wf-Network wf-ty) ss-NL =
  trans input-eq (trans (parseAttrDef-after-keyword pos ASNetwork name ty
                          outer-suffix wf-ty ss-NL scope-eq)
                        pos-fold-cong)
  where
    open Trace pos ASNetwork name ty outer-suffix
    -- ASNetwork: emitScopePrefix-chars = []; parseOptionalStandardScope
    -- falls through to `pure ASNetwork`.
    scope-eq : parseOptionalStandardScope pos2 body-after-WS1
              ≡ just (mkResult ASNetwork pos3 body-after-scope)
    scope-eq = parseOptionalStandardScope-ASNetwork-roundtrip pos2 body-after-scope
                 (parseStandardScope-fail-on-quote pos2 name body-after-name)

    -- Reshape `emitAttrDef-chars d ++ outer-suffix` to the canonical form.
    -- Step 1: apply the shape lemma to expose the unfolded structure.
    -- Step 2: rewrite via ++ₗ-assoc to push outer-suffix through the
    -- nested ++ chunks.
    input-eq : parseAttrDef pos
                 (emitAttrDef-chars (mkAttrDef name ASNetwork ty) ++ₗ outer-suffix)
               ≡ parseAttrDef pos
                 ('B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ body-after-keyword)
    input-eq = cong (parseAttrDef pos) input-list-eq
      where
        input-list-eq :
          emitAttrDef-chars (mkAttrDef name ASNetwork ty) ++ₗ outer-suffix
          ≡ 'B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ body-after-keyword
        input-list-eq =
          trans (cong (λ shape → shape ++ₗ outer-suffix)
                       (emitAttrDef-NotRel-shape name ASNetwork ty refl))
            -- After shape: (toList "BA_DEF_ " ++ [] ++ cs-name ++
            -- ' ' ∷ cs-type ++ toList " ;\n") ++ outer-suffix.
            -- Push outer-suffix through 3 ++ levels via ++ₗ-assoc.
            (trans (++ₗ-assoc (toList "BA_DEF_ ")
                              (emitScopePrefix-chars ASNetwork ++ₗ
                                cs-name ++ₗ ' ' ∷ cs-type ++ₗ toList " ;\n")
                              outer-suffix)
              (cong (toList "BA_DEF_ " ++ₗ_)
                (trans (++ₗ-assoc (emitScopePrefix-chars ASNetwork)
                                   (cs-name ++ₗ ' ' ∷ cs-type ++ₗ toList " ;\n")
                                   outer-suffix)
                  (cong (emitScopePrefix-chars ASNetwork ++ₗ_)
                    (trans (++ₗ-assoc cs-name
                                       (' ' ∷ cs-type ++ₗ toList " ;\n")
                                       outer-suffix)
                      (cong (cs-name ++ₗ_)
                        (cong (' ' ∷_)
                          (++ₗ-assoc cs-type (toList " ;\n") outer-suffix))))))))

    -- Fold the position trace `pos9` into `advancePositions pos
    -- (emitAttrDef-chars d)`.  Six advancePositions-++ steps to align
    -- the chunked structure.
    pos-fold-cong :
      just (mkResult (mkAttrDef name ASNetwork ty) pos9 outer-suffix)
      ≡ just (mkResult (mkAttrDef name ASNetwork ty)
                (advancePositions pos
                  (emitAttrDef-chars (mkAttrDef name ASNetwork ty)))
                outer-suffix)
    pos-fold-cong =
      cong (λ p → just (mkResult (mkAttrDef name ASNetwork ty) p outer-suffix))
           pos-eq
      where
        pos-eq : pos9 ≡ advancePositions pos
                          (emitAttrDef-chars (mkAttrDef name ASNetwork ty))
        pos-eq =
          sym (trans
            (advancePositions-++ pos (toList "BA_DEF_ ")
              (cs-name ++ₗ ' ' ∷ cs-type ++ₗ toList " ;\n"))
            (trans
              (advancePositions-++ (advancePositions pos (toList "BA_DEF_ "))
                cs-name (' ' ∷ cs-type ++ₗ toList " ;\n"))
              (trans
                (advancePositions-++
                  (advancePositions (advancePositions pos (toList "BA_DEF_ "))
                    cs-name)
                  (' ' ∷ cs-type) (toList " ;\n"))
                refl)))


parseAttrDef-roundtrip
  (mkAttrDef name ASNode ty) pos outer-suffix (Wf-Node wf-ty) ss-NL =
  trans input-eq (trans (parseAttrDef-after-keyword pos ASNode name ty
                          outer-suffix wf-ty ss-NL scope-eq)
                        pos-fold-cong)
  where
    open Trace pos ASNode name ty outer-suffix
    scope-eq : parseOptionalStandardScope pos2 body-after-WS1
              ≡ just (mkResult ASNode pos3 body-after-scope)
    scope-eq = parseOptionalStandardScope-ASNode-roundtrip pos2 body-after-scope
                 (∷-stop refl)

    input-eq : parseAttrDef pos
                 (emitAttrDef-chars (mkAttrDef name ASNode ty) ++ₗ outer-suffix)
               ≡ parseAttrDef pos
                 ('B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ body-after-keyword)
    input-eq = cong (parseAttrDef pos) input-list-eq
      where
        input-list-eq :
          emitAttrDef-chars (mkAttrDef name ASNode ty) ++ₗ outer-suffix
          ≡ 'B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ body-after-keyword
        input-list-eq =
          trans (cong (λ shape → shape ++ₗ outer-suffix)
                       (emitAttrDef-NotRel-shape name ASNode ty refl))
            (trans (++ₗ-assoc (toList "BA_DEF_ ")
                              (emitScopePrefix-chars ASNode ++ₗ
                                cs-name ++ₗ ' ' ∷ cs-type ++ₗ toList " ;\n")
                              outer-suffix)
              (cong (toList "BA_DEF_ " ++ₗ_)
                (trans (++ₗ-assoc (emitScopePrefix-chars ASNode)
                                   (cs-name ++ₗ ' ' ∷ cs-type ++ₗ toList " ;\n")
                                   outer-suffix)
                  (cong (emitScopePrefix-chars ASNode ++ₗ_)
                    (trans (++ₗ-assoc cs-name
                                       (' ' ∷ cs-type ++ₗ toList " ;\n")
                                       outer-suffix)
                      (cong (cs-name ++ₗ_)
                        (cong (' ' ∷_)
                          (++ₗ-assoc cs-type (toList " ;\n") outer-suffix))))))))

    pos-fold-cong :
      just (mkResult (mkAttrDef name ASNode ty) pos9 outer-suffix)
      ≡ just (mkResult (mkAttrDef name ASNode ty)
                (advancePositions pos
                  (emitAttrDef-chars (mkAttrDef name ASNode ty)))
                outer-suffix)
    pos-fold-cong =
      cong (λ p → just (mkResult (mkAttrDef name ASNode ty) p outer-suffix))
           pos-eq
      where
        pos-eq : pos9 ≡ advancePositions pos
                          (emitAttrDef-chars (mkAttrDef name ASNode ty))
        pos-eq =
          trans pos9-direct
            (sym (cong (advancePositions pos)
                       (emitAttrDef-NotRel-shape name ASNode ty refl)))
          where
            -- `pos9 ≡ advancePositions pos (toList "BA_DEF_ " ++
            -- emitScopePrefix-chars ASNode ++ cs-name ++ ' ' ∷ cs-type
            -- ++ toList " ;\n")`.  Five advancePositions-++ steps.
            pos9-direct : pos9 ≡ advancePositions pos
                                  (toList "BA_DEF_ " ++ₗ
                                    emitScopePrefix-chars ASNode ++ₗ
                                    cs-name ++ₗ ' ' ∷ cs-type ++ₗ toList " ;\n")
            pos9-direct =
              sym (trans
                (advancePositions-++ pos (toList "BA_DEF_ ")
                  (emitScopePrefix-chars ASNode ++ₗ cs-name ++ₗ
                    ' ' ∷ cs-type ++ₗ toList " ;\n"))
                (trans
                  (advancePositions-++ (advancePositions pos (toList "BA_DEF_ "))
                    (emitScopePrefix-chars ASNode)
                    (cs-name ++ₗ ' ' ∷ cs-type ++ₗ toList " ;\n"))
                  (trans
                    (advancePositions-++
                      (advancePositions (advancePositions pos (toList "BA_DEF_ "))
                        (emitScopePrefix-chars ASNode))
                      cs-name (' ' ∷ cs-type ++ₗ toList " ;\n"))
                    (trans
                      (advancePositions-++
                        (advancePositions (advancePositions
                          (advancePositions pos (toList "BA_DEF_ "))
                          (emitScopePrefix-chars ASNode))
                          cs-name)
                        (' ' ∷ cs-type) (toList " ;\n"))
                      refl))))

parseAttrDef-roundtrip
  (mkAttrDef name ASMessage ty) pos outer-suffix (Wf-Message wf-ty) ss-NL =
  trans input-eq (trans (parseAttrDef-after-keyword pos ASMessage name ty
                          outer-suffix wf-ty ss-NL scope-eq)
                        pos-fold-cong)
  where
    open Trace pos ASMessage name ty outer-suffix
    scope-eq : parseOptionalStandardScope pos2 body-after-WS1
              ≡ just (mkResult ASMessage pos3 body-after-scope)
    scope-eq = parseOptionalStandardScope-ASMessage-roundtrip pos2 body-after-scope
                 (∷-stop refl)

    input-eq : parseAttrDef pos
                 (emitAttrDef-chars (mkAttrDef name ASMessage ty) ++ₗ outer-suffix)
               ≡ parseAttrDef pos
                 ('B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ body-after-keyword)
    input-eq = cong (parseAttrDef pos) input-list-eq
      where
        input-list-eq :
          emitAttrDef-chars (mkAttrDef name ASMessage ty) ++ₗ outer-suffix
          ≡ 'B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ body-after-keyword
        input-list-eq =
          trans (cong (λ shape → shape ++ₗ outer-suffix)
                       (emitAttrDef-NotRel-shape name ASMessage ty refl))
            (trans (++ₗ-assoc (toList "BA_DEF_ ")
                              (emitScopePrefix-chars ASMessage ++ₗ
                                cs-name ++ₗ ' ' ∷ cs-type ++ₗ toList " ;\n")
                              outer-suffix)
              (cong (toList "BA_DEF_ " ++ₗ_)
                (trans (++ₗ-assoc (emitScopePrefix-chars ASMessage)
                                   (cs-name ++ₗ ' ' ∷ cs-type ++ₗ toList " ;\n")
                                   outer-suffix)
                  (cong (emitScopePrefix-chars ASMessage ++ₗ_)
                    (trans (++ₗ-assoc cs-name
                                       (' ' ∷ cs-type ++ₗ toList " ;\n")
                                       outer-suffix)
                      (cong (cs-name ++ₗ_)
                        (cong (' ' ∷_)
                          (++ₗ-assoc cs-type (toList " ;\n") outer-suffix))))))))

    pos-fold-cong :
      just (mkResult (mkAttrDef name ASMessage ty) pos9 outer-suffix)
      ≡ just (mkResult (mkAttrDef name ASMessage ty)
                (advancePositions pos
                  (emitAttrDef-chars (mkAttrDef name ASMessage ty)))
                outer-suffix)
    pos-fold-cong =
      cong (λ p → just (mkResult (mkAttrDef name ASMessage ty) p outer-suffix))
           (trans pos9-direct
             (sym (cong (advancePositions pos)
                        (emitAttrDef-NotRel-shape name ASMessage ty refl))))
      where
        pos9-direct : pos9 ≡ advancePositions pos
                              (toList "BA_DEF_ " ++ₗ
                                emitScopePrefix-chars ASMessage ++ₗ
                                cs-name ++ₗ ' ' ∷ cs-type ++ₗ toList " ;\n")
        pos9-direct =
          sym (trans
            (advancePositions-++ pos (toList "BA_DEF_ ")
              (emitScopePrefix-chars ASMessage ++ₗ cs-name ++ₗ
                ' ' ∷ cs-type ++ₗ toList " ;\n"))
            (trans
              (advancePositions-++ (advancePositions pos (toList "BA_DEF_ "))
                (emitScopePrefix-chars ASMessage)
                (cs-name ++ₗ ' ' ∷ cs-type ++ₗ toList " ;\n"))
              (trans
                (advancePositions-++
                  (advancePositions (advancePositions pos (toList "BA_DEF_ "))
                    (emitScopePrefix-chars ASMessage))
                  cs-name (' ' ∷ cs-type ++ₗ toList " ;\n"))
                (trans
                  (advancePositions-++
                    (advancePositions (advancePositions
                      (advancePositions pos (toList "BA_DEF_ "))
                      (emitScopePrefix-chars ASMessage))
                      cs-name)
                    (' ' ∷ cs-type) (toList " ;\n"))
                  refl))))

parseAttrDef-roundtrip
  (mkAttrDef name ASSignal ty) pos outer-suffix (Wf-Signal wf-ty) ss-NL =
  trans input-eq (trans (parseAttrDef-after-keyword pos ASSignal name ty
                          outer-suffix wf-ty ss-NL scope-eq)
                        pos-fold-cong)
  where
    open Trace pos ASSignal name ty outer-suffix
    scope-eq : parseOptionalStandardScope pos2 body-after-WS1
              ≡ just (mkResult ASSignal pos3 body-after-scope)
    scope-eq = parseOptionalStandardScope-ASSignal-roundtrip pos2 body-after-scope
                 (∷-stop refl)

    input-eq : parseAttrDef pos
                 (emitAttrDef-chars (mkAttrDef name ASSignal ty) ++ₗ outer-suffix)
               ≡ parseAttrDef pos
                 ('B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ body-after-keyword)
    input-eq = cong (parseAttrDef pos) input-list-eq
      where
        input-list-eq :
          emitAttrDef-chars (mkAttrDef name ASSignal ty) ++ₗ outer-suffix
          ≡ 'B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ body-after-keyword
        input-list-eq =
          trans (cong (λ shape → shape ++ₗ outer-suffix)
                       (emitAttrDef-NotRel-shape name ASSignal ty refl))
            (trans (++ₗ-assoc (toList "BA_DEF_ ")
                              (emitScopePrefix-chars ASSignal ++ₗ
                                cs-name ++ₗ ' ' ∷ cs-type ++ₗ toList " ;\n")
                              outer-suffix)
              (cong (toList "BA_DEF_ " ++ₗ_)
                (trans (++ₗ-assoc (emitScopePrefix-chars ASSignal)
                                   (cs-name ++ₗ ' ' ∷ cs-type ++ₗ toList " ;\n")
                                   outer-suffix)
                  (cong (emitScopePrefix-chars ASSignal ++ₗ_)
                    (trans (++ₗ-assoc cs-name
                                       (' ' ∷ cs-type ++ₗ toList " ;\n")
                                       outer-suffix)
                      (cong (cs-name ++ₗ_)
                        (cong (' ' ∷_)
                          (++ₗ-assoc cs-type (toList " ;\n") outer-suffix))))))))

    pos-fold-cong :
      just (mkResult (mkAttrDef name ASSignal ty) pos9 outer-suffix)
      ≡ just (mkResult (mkAttrDef name ASSignal ty)
                (advancePositions pos
                  (emitAttrDef-chars (mkAttrDef name ASSignal ty)))
                outer-suffix)
    pos-fold-cong =
      cong (λ p → just (mkResult (mkAttrDef name ASSignal ty) p outer-suffix))
           (trans pos9-direct
             (sym (cong (advancePositions pos)
                        (emitAttrDef-NotRel-shape name ASSignal ty refl))))
      where
        pos9-direct : pos9 ≡ advancePositions pos
                              (toList "BA_DEF_ " ++ₗ
                                emitScopePrefix-chars ASSignal ++ₗ
                                cs-name ++ₗ ' ' ∷ cs-type ++ₗ toList " ;\n")
        pos9-direct =
          sym (trans
            (advancePositions-++ pos (toList "BA_DEF_ ")
              (emitScopePrefix-chars ASSignal ++ₗ cs-name ++ₗ
                ' ' ∷ cs-type ++ₗ toList " ;\n"))
            (trans
              (advancePositions-++ (advancePositions pos (toList "BA_DEF_ "))
                (emitScopePrefix-chars ASSignal)
                (cs-name ++ₗ ' ' ∷ cs-type ++ₗ toList " ;\n"))
              (trans
                (advancePositions-++
                  (advancePositions (advancePositions pos (toList "BA_DEF_ "))
                    (emitScopePrefix-chars ASSignal))
                  cs-name (' ' ∷ cs-type ++ₗ toList " ;\n"))
                (trans
                  (advancePositions-++
                    (advancePositions (advancePositions
                      (advancePositions pos (toList "BA_DEF_ "))
                      (emitScopePrefix-chars ASSignal))
                      cs-name)
                    (' ' ∷ cs-type) (toList " ;\n"))
                  refl))))

parseAttrDef-roundtrip
  (mkAttrDef name ASEnvVar ty) pos outer-suffix (Wf-EnvVar wf-ty) ss-NL =
  trans input-eq (trans (parseAttrDef-after-keyword pos ASEnvVar name ty
                          outer-suffix wf-ty ss-NL scope-eq)
                        pos-fold-cong)
  where
    open Trace pos ASEnvVar name ty outer-suffix
    scope-eq : parseOptionalStandardScope pos2 body-after-WS1
              ≡ just (mkResult ASEnvVar pos3 body-after-scope)
    scope-eq = parseOptionalStandardScope-ASEnvVar-roundtrip pos2 body-after-scope
                 (∷-stop refl)

    input-eq : parseAttrDef pos
                 (emitAttrDef-chars (mkAttrDef name ASEnvVar ty) ++ₗ outer-suffix)
               ≡ parseAttrDef pos
                 ('B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ body-after-keyword)
    input-eq = cong (parseAttrDef pos) input-list-eq
      where
        input-list-eq :
          emitAttrDef-chars (mkAttrDef name ASEnvVar ty) ++ₗ outer-suffix
          ≡ 'B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ body-after-keyword
        input-list-eq =
          trans (cong (λ shape → shape ++ₗ outer-suffix)
                       (emitAttrDef-NotRel-shape name ASEnvVar ty refl))
            (trans (++ₗ-assoc (toList "BA_DEF_ ")
                              (emitScopePrefix-chars ASEnvVar ++ₗ
                                cs-name ++ₗ ' ' ∷ cs-type ++ₗ toList " ;\n")
                              outer-suffix)
              (cong (toList "BA_DEF_ " ++ₗ_)
                (trans (++ₗ-assoc (emitScopePrefix-chars ASEnvVar)
                                   (cs-name ++ₗ ' ' ∷ cs-type ++ₗ toList " ;\n")
                                   outer-suffix)
                  (cong (emitScopePrefix-chars ASEnvVar ++ₗ_)
                    (trans (++ₗ-assoc cs-name
                                       (' ' ∷ cs-type ++ₗ toList " ;\n")
                                       outer-suffix)
                      (cong (cs-name ++ₗ_)
                        (cong (' ' ∷_)
                          (++ₗ-assoc cs-type (toList " ;\n") outer-suffix))))))))

    pos-fold-cong :
      just (mkResult (mkAttrDef name ASEnvVar ty) pos9 outer-suffix)
      ≡ just (mkResult (mkAttrDef name ASEnvVar ty)
                (advancePositions pos
                  (emitAttrDef-chars (mkAttrDef name ASEnvVar ty)))
                outer-suffix)
    pos-fold-cong =
      cong (λ p → just (mkResult (mkAttrDef name ASEnvVar ty) p outer-suffix))
           (trans pos9-direct
             (sym (cong (advancePositions pos)
                        (emitAttrDef-NotRel-shape name ASEnvVar ty refl))))
      where
        pos9-direct : pos9 ≡ advancePositions pos
                              (toList "BA_DEF_ " ++ₗ
                                emitScopePrefix-chars ASEnvVar ++ₗ
                                cs-name ++ₗ ' ' ∷ cs-type ++ₗ toList " ;\n")
        pos9-direct =
          sym (trans
            (advancePositions-++ pos (toList "BA_DEF_ ")
              (emitScopePrefix-chars ASEnvVar ++ₗ cs-name ++ₗ
                ' ' ∷ cs-type ++ₗ toList " ;\n"))
            (trans
              (advancePositions-++ (advancePositions pos (toList "BA_DEF_ "))
                (emitScopePrefix-chars ASEnvVar)
                (cs-name ++ₗ ' ' ∷ cs-type ++ₗ toList " ;\n"))
              (trans
                (advancePositions-++
                  (advancePositions (advancePositions pos (toList "BA_DEF_ "))
                    (emitScopePrefix-chars ASEnvVar))
                  cs-name (' ' ∷ cs-type ++ₗ toList " ;\n"))
                (trans
                  (advancePositions-++
                    (advancePositions (advancePositions
                      (advancePositions pos (toList "BA_DEF_ "))
                      (emitScopePrefix-chars ASEnvVar))
                      cs-name)
                    (' ' ∷ cs-type) (toList " ;\n"))
                  refl))))


-- ============================================================================
-- parseAttrDefRel-roundtrip — `BA_DEF_REL_` per-line construct
-- ============================================================================
--
-- `parseAttrDefRel` is the rel-scope (`isRelScope ≡ true`) variant.
-- The bind chain has one more step than `parseAttrDef` because
-- `parseAttrDefRel` calls `parseRelScope >>= parseWS` separately rather
-- than via `parseOptionalStandardScope`'s embedded `<* parseWS`.

-- Witness that `AttrDef.scope d` is a rel scope.
data WfAttrDef-Rel : AttrDef → Set where
  Wf-NodeMsg : ∀ {n ty} → WfAttrType ty → WfAttrDef-Rel (mkAttrDef n ASNodeMsg ty)
  Wf-NodeSig : ∀ {n ty} → WfAttrType ty → WfAttrDef-Rel (mkAttrDef n ASNodeSig ty)

-- Helper: shape `emitAttrDef-chars d` when scope is rel.
emitAttrDef-Rel-shape : ∀ (name : String) (scope : AttrScope) (ty : AttrType)
  → isRelScope scope ≡ true
  → emitAttrDef-chars (mkAttrDef name scope ty)
    ≡ toList "BA_DEF_REL_ " ++ₗ emitScopePrefix-chars scope ++ₗ
      quoteStringLit-chars name ++ₗ
      ' ' ∷ emitAttrType-chars ty ++ₗ toList " ;\n"
emitAttrDef-Rel-shape _ ASNetwork _ ()
emitAttrDef-Rel-shape _ ASNode    _ ()
emitAttrDef-Rel-shape _ ASMessage _ ()
emitAttrDef-Rel-shape _ ASSignal  _ ()
emitAttrDef-Rel-shape _ ASEnvVar  _ ()
emitAttrDef-Rel-shape name ASNodeMsg ty refl = refl
emitAttrDef-Rel-shape name ASNodeSig ty refl = refl

-- Per-tag parseRelScope helpers (no trailing parseWS — that step is
-- a separate bind in parseAttrDefRel).
private
  parseRelScope-ASNodeMsg-eq : ∀ pos rest
    → parseRelScope pos
        ('B' ∷ 'U' ∷ '_' ∷ 'B' ∷ 'O' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷ rest)
      ≡ just (mkResult ASNodeMsg
                (advancePositions pos (toList "BU_BO_REL_"))
                rest)
  parseRelScope-ASNodeMsg-eq pos rest =
    alt-left-just (string "BU_BO_REL_" *> pure ASNodeMsg)
                  (string "BU_SG_REL_" *> pure ASNodeSig)
                  pos
                  ('B' ∷ 'U' ∷ '_' ∷ 'B' ∷ 'O' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷ rest)
                  _
                  (string-*>-success pos "BU_BO_REL_" ASNodeMsg rest)

  parseRelScope-ASNodeSig-eq : ∀ pos rest
    → parseRelScope pos
        ('B' ∷ 'U' ∷ '_' ∷ 'S' ∷ 'G' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷ rest)
      ≡ just (mkResult ASNodeSig
                (advancePositions pos (toList "BU_SG_REL_"))
                rest)
  parseRelScope-ASNodeSig-eq pos rest =
    trans (alt-right-nothing
             (string "BU_BO_REL_" *> pure ASNodeMsg)
             (string "BU_SG_REL_" *> pure ASNodeSig)
             pos
             ('B' ∷ 'U' ∷ '_' ∷ 'S' ∷ 'G' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷ rest)
             refl)
          (string-*>-success pos "BU_SG_REL_" ASNodeSig rest)

-- Trace for parseAttrDefRel.  The bind chain has 11 steps (one more
-- than parseAttrDef because parseRelScope and the post-scope parseWS
-- are separate binds).
private
  cs-scope-kw-of : AttrScope → List Char
  cs-scope-kw-of ASNodeMsg = 'B' ∷ 'U' ∷ '_' ∷ 'B' ∷ 'O' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷ []
  cs-scope-kw-of ASNodeSig = 'B' ∷ 'U' ∷ '_' ∷ 'S' ∷ 'G' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷ []
  cs-scope-kw-of _         = []

  module TraceRel (pos : Position) (scope : AttrScope)
                  (name : String) (ty : AttrType)
                  (outer-suffix : List Char) where
    cs-scope-kw : List Char
    cs-scope-kw = cs-scope-kw-of scope

    cs-name = quoteStringLit-chars name
    cs-type = emitAttrType-chars ty
    cs-tail = toList " ;\n"

    pos1 : Position  -- after string "BA_DEF_REL_"
    pos1 = advancePositions pos (toList "BA_DEF_REL_")

    pos2 : Position  -- after parseWS (1 space)
    pos2 = advancePosition pos1 ' '

    pos3 : Position  -- after parseRelScope (10 chars)
    pos3 = advancePositions pos2 cs-scope-kw

    pos4 : Position  -- after parseWS (1 space)
    pos4 = advancePosition pos3 ' '

    pos5 : Position  -- after parseStringLit
    pos5 = advancePositions pos4 cs-name

    pos6 : Position  -- after parseWS (1 space)
    pos6 = advancePosition pos5 ' '

    pos7 : Position  -- after parseAttrTypeDecl
    pos7 = advancePositions pos6 cs-type

    pos8 : Position  -- after parseWSOpt (1 space)
    pos8 = advancePosition pos7 ' '

    pos9 : Position  -- after char ';'
    pos9 = advancePosition pos8 ';'

    pos10 : Position  -- after parseNewline
    pos10 = advancePosition pos9 '\n'

    -- Input slices.
    rest-tail : List Char
    rest-tail = ' ' ∷ ';' ∷ '\n' ∷ outer-suffix

    body-after-keyword : List Char
    body-after-keyword =
      ' ' ∷ cs-scope-kw ++ₗ ' ' ∷ cs-name ++ₗ ' ' ∷ cs-type ++ₗ rest-tail

    body-after-WS1 : List Char
    body-after-WS1 = cs-scope-kw ++ₗ ' ' ∷ cs-name ++ₗ ' ' ∷ cs-type ++ₗ rest-tail

    body-after-scope : List Char
    body-after-scope = ' ' ∷ cs-name ++ₗ ' ' ∷ cs-type ++ₗ rest-tail

    body-after-WS2 : List Char
    body-after-WS2 = cs-name ++ₗ ' ' ∷ cs-type ++ₗ rest-tail

    body-after-name : List Char
    body-after-name = ' ' ∷ cs-type ++ₗ rest-tail

    body-after-WS3 : List Char
    body-after-WS3 = cs-type ++ₗ rest-tail

    body-after-type : List Char
    body-after-type = rest-tail

    body-after-WSOpt : List Char
    body-after-WSOpt = ';' ∷ '\n' ∷ outer-suffix

    body-after-semi : List Char
    body-after-semi = '\n' ∷ outer-suffix

    body-after-NL : List Char
    body-after-NL = outer-suffix


-- Parameterised inner lemma: given a `parseRelScope pos2 input ≡ just
-- (mkResult scope pos3 input')` witness, the rest of the bind chain
-- composes uniformly.  `is-rel` selects the rel-scope cases (head of
-- cs-scope-kw is 'B', non-hspace).
parseAttrDefRel-after-keyword :
  ∀ pos (scope : AttrScope) (name : String) (ty : AttrType)
    (outer-suffix : List Char)
  → WfAttrType ty
  → SuffixStops isNewlineStart outer-suffix
  → isRelScope scope ≡ true
  → let open TraceRel pos scope name ty outer-suffix in
    parseRelScope pos2 body-after-WS1
      ≡ just (mkResult scope pos3 body-after-scope)
  → parseAttrDefRel pos
      ('B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷
        TraceRel.body-after-keyword pos scope name ty outer-suffix)
    ≡ just (mkResult (mkAttrDef name scope ty)
              (TraceRel.pos10 pos scope name ty outer-suffix)
              outer-suffix)
parseAttrDefRel-after-keyword pos scope name ty outer-suffix wf-ty ss-NL is-rel scope-eq =
    -- Step 1: string "BA_DEF_REL_"
    trans (bind-just-step (string "BA_DEF_REL_")
           (λ _ → parseWS >>= λ _ →
                  parseRelScope >>= λ s →
                  parseWS >>= λ _ →
                  parseStringLit >>= λ n →
                  parseWS >>= λ _ →
                  parseAttrTypeDecl >>= λ ty₁ →
                  parseWSOpt >>= λ _ →
                  char ';' >>= λ _ →
                  parseNewline >>= λ _ →
                  many parseNewline >>= λ _ →
                  pure (mkAttrDef n s ty₁))
           pos
           ('B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷
            body-after-keyword)
           "BA_DEF_REL_" pos1 body-after-keyword
           (string-success pos "BA_DEF_REL_" body-after-keyword))
    -- Step 2: parseWS consumes ' '.
    (trans (bind-just-step parseWS
              (λ _ → parseRelScope >>= λ s →
                     parseWS >>= λ _ →
                     parseStringLit >>= λ n →
                     parseWS >>= λ _ →
                     parseAttrTypeDecl >>= λ ty₁ →
                     parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkAttrDef n s ty₁))
              pos1 body-after-keyword
              (' ' ∷ []) pos2 body-after-WS1
              (parseWS-one-space pos1 body-after-WS1
                (scope-kw-stops-isHSpace scope is-rel name)))
    -- Step 3: parseRelScope (scope-eq witness).
    (trans (bind-just-step parseRelScope
              (λ s → parseWS >>= λ _ →
                     parseStringLit >>= λ n →
                     parseWS >>= λ _ →
                     parseAttrTypeDecl >>= λ ty₁ →
                     parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkAttrDef n s ty₁))
              pos2 body-after-WS1
              scope pos3 body-after-scope
              scope-eq)
    -- Step 4: parseWS consumes the post-scope ' '.
    (trans (bind-just-step parseWS
              (λ _ → parseStringLit >>= λ n →
                     parseWS >>= λ _ →
                     parseAttrTypeDecl >>= λ ty₁ →
                     parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkAttrDef n scope ty₁))
              pos3 body-after-scope
              (' ' ∷ []) pos4 body-after-WS2
              (parseWS-one-space pos3 body-after-WS2 (∷-stop refl)))
    -- Step 5: parseStringLit reads name.
    (trans (bind-just-step parseStringLit
              (λ n → parseWS >>= λ _ →
                     parseAttrTypeDecl >>= λ ty₁ →
                     parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkAttrDef n scope ty₁))
              pos4 body-after-WS2
              name pos5 body-after-name
              (parseStringLit-roundtrip pos4 name body-after-name (∷-stop refl)))
    -- Step 6: parseWS consumes ' '.
    (trans (bind-just-step parseWS
              (λ _ → parseAttrTypeDecl >>= λ ty₁ →
                     parseWSOpt >>= λ _ →
                     char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkAttrDef name scope ty₁))
              pos5 body-after-name
              (' ' ∷ []) pos6 body-after-WS3
              (parseWS-one-space pos5 body-after-WS3
                (attrType-emit-stops-isHSpace ty rest-tail)))
    -- Step 7: parseAttrTypeDecl reads ty.
    (trans (bind-just-step parseAttrTypeDecl
              (λ ty₁ → parseWSOpt >>= λ _ →
                       char ';' >>= λ _ →
                       parseNewline >>= λ _ →
                       many parseNewline >>= λ _ →
                       pure (mkAttrDef name scope ty₁))
              pos6 body-after-WS3
              ty pos7 body-after-type
              (parseAttrTypeDecl-roundtrip pos6 (';' ∷ '\n' ∷ outer-suffix) wf-ty))
    -- Step 8: parseWSOpt consumes ' '.
    (trans (bind-just-step parseWSOpt
              (λ _ → char ';' >>= λ _ →
                     parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkAttrDef name scope ty))
              pos7 body-after-type
              (' ' ∷ []) pos8 body-after-WSOpt
              (parseWSOpt-step pos7 outer-suffix))
    -- Step 9: char ';'.
    (trans (bind-just-step (char ';')
              (λ _ → parseNewline >>= λ _ →
                     many parseNewline >>= λ _ →
                     pure (mkAttrDef name scope ty))
              pos8 body-after-WSOpt
              ';' pos9 body-after-semi
              refl)
    -- Step 10: parseNewline.
    (trans (bind-just-step parseNewline
              (λ _ → many parseNewline >>= λ _ →
                     pure (mkAttrDef name scope ty))
              pos9 body-after-semi
              '\n' pos10 body-after-NL
              (parseNewline-match-LF pos9 outer-suffix))
    -- Step 11: many parseNewline.
    (trans (bind-just-step (many parseNewline)
              (λ _ → pure (mkAttrDef name scope ty))
              pos10 body-after-NL
              [] pos10 outer-suffix
              (manyHelper-parseNewline-exhaust pos10 outer-suffix
                (length outer-suffix) ss-NL))
      refl))))))))))
  where
    open TraceRel pos scope name ty outer-suffix

    -- After "BA_DEF_REL_ ", input is the rel-scope keyword `'B' ∷ 'U'
    -- ∷ '_' ∷ ...`.  For rel scopes (only reachable cases per
    -- `is-rel`), head is 'B' (non-hspace).  Non-rel scopes are
    -- excluded via absurd patterns on `is-rel`.
    scope-kw-stops-isHSpace : ∀ (scp : AttrScope)
      → isRelScope scp ≡ true
      → ∀ (s : String)
      → SuffixStops isHSpace
          (cs-scope-kw-of scp ++ₗ
            ' ' ∷ quoteStringLit-chars s ++ₗ ' ' ∷ emitAttrType-chars ty ++ₗ
              ' ' ∷ ';' ∷ '\n' ∷ outer-suffix)
    scope-kw-stops-isHSpace ASNodeMsg refl _ = ∷-stop refl
    scope-kw-stops-isHSpace ASNodeSig refl _ = ∷-stop refl
    scope-kw-stops-isHSpace ASNetwork ()
    scope-kw-stops-isHSpace ASNode    ()
    scope-kw-stops-isHSpace ASMessage ()
    scope-kw-stops-isHSpace ASSignal  ()
    scope-kw-stops-isHSpace ASEnvVar  ()

    attrType-emit-stops-isHSpace :
      ∀ (ty₁ : AttrType) (rest : List Char)
      → SuffixStops isHSpace (emitAttrType-chars ty₁ ++ₗ rest)
    attrType-emit-stops-isHSpace (ATInt _ _)   _ = ∷-stop refl
    attrType-emit-stops-isHSpace (ATFloat _ _) _ = ∷-stop refl
    attrType-emit-stops-isHSpace ATString      _ = ∷-stop refl
    attrType-emit-stops-isHSpace (ATEnum _)    _ = ∷-stop refl
    attrType-emit-stops-isHSpace (ATHex _ _)   _ = ∷-stop refl

    parseWSOpt-step :
      ∀ (p : Position) (rest : List Char) →
      parseWSOpt p (' ' ∷ ';' ∷ '\n' ∷ rest)
      ≡ just (mkResult (' ' ∷ [])
              (advancePosition p ' ')
              (';' ∷ '\n' ∷ rest))
    parseWSOpt-step p rest =
      manyHelper-satisfy-exhaust-many isHSpace
        p (' ' ∷ []) (';' ∷ '\n' ∷ rest)
        (refl AllList.∷ AllList.[])
        (∷-stop refl)
      where
        import Data.List.Relation.Unary.All as AllList


-- ============================================================================
-- parseAttrDefRel-roundtrip — top-level dispatcher
-- ============================================================================

parseAttrDefRel-roundtrip : ∀ (d : AttrDef) (pos : Position) (outer-suffix : List Char)
  → WfAttrDef-Rel d
  → SuffixStops isNewlineStart outer-suffix
  → parseAttrDefRel pos (emitAttrDef-chars d ++ₗ outer-suffix)
    ≡ just (mkResult d
              (advancePositions pos (emitAttrDef-chars d))
              outer-suffix)
parseAttrDefRel-roundtrip
  (mkAttrDef name ASNodeMsg ty) pos outer-suffix (Wf-NodeMsg wf-ty) ss-NL =
  trans input-eq (trans (parseAttrDefRel-after-keyword pos ASNodeMsg name ty
                          outer-suffix wf-ty ss-NL refl scope-eq)
                        pos-fold-cong)
  where
    open TraceRel pos ASNodeMsg name ty outer-suffix
    scope-eq : parseRelScope pos2 body-after-WS1
              ≡ just (mkResult ASNodeMsg pos3 body-after-scope)
    scope-eq = parseRelScope-ASNodeMsg-eq pos2
                 (' ' ∷ cs-name ++ₗ ' ' ∷ cs-type ++ₗ rest-tail)

    input-eq : parseAttrDefRel pos
                 (emitAttrDef-chars (mkAttrDef name ASNodeMsg ty) ++ₗ outer-suffix)
               ≡ parseAttrDefRel pos
                 ('B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷
                  body-after-keyword)
    input-eq = cong (parseAttrDefRel pos) input-list-eq
      where
        input-list-eq :
          emitAttrDef-chars (mkAttrDef name ASNodeMsg ty) ++ₗ outer-suffix
          ≡ 'B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷
            body-after-keyword
        input-list-eq =
          trans (cong (λ shape → shape ++ₗ outer-suffix)
                       (emitAttrDef-Rel-shape name ASNodeMsg ty refl))
            (trans (++ₗ-assoc (toList "BA_DEF_REL_ ")
                              (emitScopePrefix-chars ASNodeMsg ++ₗ
                                cs-name ++ₗ ' ' ∷ cs-type ++ₗ toList " ;\n")
                              outer-suffix)
              (cong (toList "BA_DEF_REL_ " ++ₗ_)
                (trans (++ₗ-assoc (emitScopePrefix-chars ASNodeMsg)
                                   (cs-name ++ₗ ' ' ∷ cs-type ++ₗ toList " ;\n")
                                   outer-suffix)
                  (cong (emitScopePrefix-chars ASNodeMsg ++ₗ_)
                    (trans (++ₗ-assoc cs-name
                                       (' ' ∷ cs-type ++ₗ toList " ;\n")
                                       outer-suffix)
                      (cong (cs-name ++ₗ_)
                        (cong (' ' ∷_)
                          (++ₗ-assoc cs-type (toList " ;\n") outer-suffix))))))))

    pos-fold-cong :
      just (mkResult (mkAttrDef name ASNodeMsg ty) pos10 outer-suffix)
      ≡ just (mkResult (mkAttrDef name ASNodeMsg ty)
                (advancePositions pos
                  (emitAttrDef-chars (mkAttrDef name ASNodeMsg ty)))
                outer-suffix)
    pos-fold-cong =
      cong (λ p → just (mkResult (mkAttrDef name ASNodeMsg ty) p outer-suffix))
           (trans pos10-direct
             (sym (cong (advancePositions pos)
                        (emitAttrDef-Rel-shape name ASNodeMsg ty refl))))
      where
        pos10-direct : pos10 ≡ advancePositions pos
                                (toList "BA_DEF_REL_ " ++ₗ
                                  emitScopePrefix-chars ASNodeMsg ++ₗ
                                  cs-name ++ₗ ' ' ∷ cs-type ++ₗ toList " ;\n")
        pos10-direct =
          sym (trans
            (advancePositions-++ pos (toList "BA_DEF_REL_ ")
              (emitScopePrefix-chars ASNodeMsg ++ₗ cs-name ++ₗ
                ' ' ∷ cs-type ++ₗ toList " ;\n"))
            (trans
              (advancePositions-++ (advancePositions pos (toList "BA_DEF_REL_ "))
                (emitScopePrefix-chars ASNodeMsg)
                (cs-name ++ₗ ' ' ∷ cs-type ++ₗ toList " ;\n"))
              (trans
                (advancePositions-++
                  (advancePositions (advancePositions pos (toList "BA_DEF_REL_ "))
                    (emitScopePrefix-chars ASNodeMsg))
                  cs-name (' ' ∷ cs-type ++ₗ toList " ;\n"))
                (trans
                  (advancePositions-++
                    (advancePositions (advancePositions
                      (advancePositions pos (toList "BA_DEF_REL_ "))
                      (emitScopePrefix-chars ASNodeMsg))
                      cs-name)
                    (' ' ∷ cs-type) (toList " ;\n"))
                  refl))))

parseAttrDefRel-roundtrip
  (mkAttrDef name ASNodeSig ty) pos outer-suffix (Wf-NodeSig wf-ty) ss-NL =
  trans input-eq (trans (parseAttrDefRel-after-keyword pos ASNodeSig name ty
                          outer-suffix wf-ty ss-NL refl scope-eq)
                        pos-fold-cong)
  where
    open TraceRel pos ASNodeSig name ty outer-suffix
    scope-eq : parseRelScope pos2 body-after-WS1
              ≡ just (mkResult ASNodeSig pos3 body-after-scope)
    scope-eq = parseRelScope-ASNodeSig-eq pos2
                 (' ' ∷ cs-name ++ₗ ' ' ∷ cs-type ++ₗ rest-tail)

    input-eq : parseAttrDefRel pos
                 (emitAttrDef-chars (mkAttrDef name ASNodeSig ty) ++ₗ outer-suffix)
               ≡ parseAttrDefRel pos
                 ('B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷
                  body-after-keyword)
    input-eq = cong (parseAttrDefRel pos) input-list-eq
      where
        input-list-eq :
          emitAttrDef-chars (mkAttrDef name ASNodeSig ty) ++ₗ outer-suffix
          ≡ 'B' ∷ 'A' ∷ '_' ∷ 'D' ∷ 'E' ∷ 'F' ∷ '_' ∷ 'R' ∷ 'E' ∷ 'L' ∷ '_' ∷
            body-after-keyword
        input-list-eq =
          trans (cong (λ shape → shape ++ₗ outer-suffix)
                       (emitAttrDef-Rel-shape name ASNodeSig ty refl))
            (trans (++ₗ-assoc (toList "BA_DEF_REL_ ")
                              (emitScopePrefix-chars ASNodeSig ++ₗ
                                cs-name ++ₗ ' ' ∷ cs-type ++ₗ toList " ;\n")
                              outer-suffix)
              (cong (toList "BA_DEF_REL_ " ++ₗ_)
                (trans (++ₗ-assoc (emitScopePrefix-chars ASNodeSig)
                                   (cs-name ++ₗ ' ' ∷ cs-type ++ₗ toList " ;\n")
                                   outer-suffix)
                  (cong (emitScopePrefix-chars ASNodeSig ++ₗ_)
                    (trans (++ₗ-assoc cs-name
                                       (' ' ∷ cs-type ++ₗ toList " ;\n")
                                       outer-suffix)
                      (cong (cs-name ++ₗ_)
                        (cong (' ' ∷_)
                          (++ₗ-assoc cs-type (toList " ;\n") outer-suffix))))))))

    pos-fold-cong :
      just (mkResult (mkAttrDef name ASNodeSig ty) pos10 outer-suffix)
      ≡ just (mkResult (mkAttrDef name ASNodeSig ty)
                (advancePositions pos
                  (emitAttrDef-chars (mkAttrDef name ASNodeSig ty)))
                outer-suffix)
    pos-fold-cong =
      cong (λ p → just (mkResult (mkAttrDef name ASNodeSig ty) p outer-suffix))
           (trans pos10-direct
             (sym (cong (advancePositions pos)
                        (emitAttrDef-Rel-shape name ASNodeSig ty refl))))
      where
        pos10-direct : pos10 ≡ advancePositions pos
                                (toList "BA_DEF_REL_ " ++ₗ
                                  emitScopePrefix-chars ASNodeSig ++ₗ
                                  cs-name ++ₗ ' ' ∷ cs-type ++ₗ toList " ;\n")
        pos10-direct =
          sym (trans
            (advancePositions-++ pos (toList "BA_DEF_REL_ ")
              (emitScopePrefix-chars ASNodeSig ++ₗ cs-name ++ₗ
                ' ' ∷ cs-type ++ₗ toList " ;\n"))
            (trans
              (advancePositions-++ (advancePositions pos (toList "BA_DEF_REL_ "))
                (emitScopePrefix-chars ASNodeSig)
                (cs-name ++ₗ ' ' ∷ cs-type ++ₗ toList " ;\n"))
              (trans
                (advancePositions-++
                  (advancePositions (advancePositions pos (toList "BA_DEF_REL_ "))
                    (emitScopePrefix-chars ASNodeSig))
                  cs-name (' ' ∷ cs-type ++ₗ toList " ;\n"))
                (trans
                  (advancePositions-++
                    (advancePositions (advancePositions
                      (advancePositions pos (toList "BA_DEF_REL_ "))
                      (emitScopePrefix-chars ASNodeSig))
                      cs-name)
                    (' ' ∷ cs-type) (toList " ;\n"))
                  refl))))
