{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.5.d — DSL-side preamble formats for the DBC text
-- format: VERSION, BS_, NS_.
--
-- The three preamble constructs share the framework-extension theme of
-- this commit: each is a wrap-shape (`parse <fmt> >>= many parseNewline
-- >>= pure`) preserving the existing permissive parser spec.  The two
-- new Format DSL constructors landed for this work are:
--
--   * `wsCanonTab`     — canonical tab emit, parser one-or-more isHSpace
--                        (mirror of `ws` for tab-indented NS_ lines).
--   * `nonNewlineRun`  — empty canonical emit, parser zero-or-more
--                        non-newline (BS_ opaque-tail consumer).
--
-- Bridge proofs (DSL emit ≡ existing formatter) are minimal:
--
--   * VERSION: `emit versionFmt v ++ '\n' ∷ [] ≡ emitVersion-chars v`
--              — formatter has trailing `\n\n`, DSL emits one `\n` and
--              the wrapper's `many parseNewline` consumes the second.
--   * BS_:     `emit bitTimingFmt tt ++ '\n' ∷ [] ≡ emitBitTiming-chars`
--              — same shape (formatter `BS_:\n\n`, DSL `BS_:\n`).
--   * NS_:     `emit nsFmt tt ≡ emitNamespace-chars` — DSL captures the
--              entire 27-newline block (header + 25 keywords + trailing
--              blank); the wrapper's `many parseNewline` consumes zero.
--
-- The NS_ body uses the discard-iso pattern: `iso (λ _ → tt) (λ _ →
-- canonical-NSLine) refl <inner-tower>`.  The inner tower's underlying
-- carrier is `⊤ × List NSLineShape`; the iso projects everything to
-- `⊤` for the user-facing API while emitting the canonical 26-element
-- body (25 specific keyword identifiers + 1 blank).  Each
-- `NSLineShape` constructor (`ns-blank` / `ns-keyword`) is dispatched
-- via `altSum` over `blankLineFmt` and `keywordLineFmt`; the
-- altSum disjointness witness for the keyword branch closes by
-- `λ _ → refl` because `parse newlineFmt` rejects `'\t'`-led input
-- definitionally.
module Aletheia.DBC.TextParser.Format.Preamble where

open import Data.Bool using (Bool; true; false; T; _∨_)
open import Data.Char using (Char; _≈ᵇ_) renaming (_≟_ to _≟ᶜ_)
open import Data.List using (List; []; _∷_; length; map) renaming (_++_ to _++ₗ_)
open import Data.List.Properties using () renaming (++-assoc to ++ₗ-assoc)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; zero; s≤s; z≤n)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax; Σ; Σ-syntax)
open import Data.String using (String; toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Aletheia.Parser.Combinators
  using (Position; Parser; ParseResult; mkResult; advancePosition; advancePositions;
         parseCharsSeq; pure; _>>=_; _<|>_; _<$>_;
         char; satisfy; manyHelper)
  renaming (many to many-parser)
open import Aletheia.DBC.Identifier using
  (Identifier; mkIdent; isIdentStart; isIdentCont; validIdentifierᵇ)
open import Aletheia.DBC.TextParser.Lexer using
  (parseWS; parseWSOpt; parseNewline; parseStringLit;
   isHSpace; isNonNewline)
open import Aletheia.DBC.TextFormatter.Emitter using (quoteStringLit-chars)
open import Aletheia.DBC.TextFormatter.Preamble using
  (emitVersion-chars; emitBitTiming-chars; emitNamespace-chars)
open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; []-stop; ∷-stop; bind-just-step;
   advancePositions-++)
open import Aletheia.DBC.TextParser.Properties.Primitives using
  (alt-right-nothing; bind-nothing; map-nothing; char-matches)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart; parseNewline-match-LF; parseNewline-fail-on-stop;
   manyHelper-parseNewline-exhaust; many-parseNewline-one-LF-stop)
open import Aletheia.DBC.TextParser.Format
  using (Format; literal; ident; pair; iso; many;
         altSum; ws; wsOpt; wsCanonOne; wsCanonTab; nonNewlineRun;
         stringLit; withPrefix;
         emit; parse; EmitsOK; EmitsOKMany; ParseFailsAt;
         []-fails; ∷-cons; roundtrip)

-- ============================================================================
-- LOCAL SUGAR — ws-aware combinators
-- ============================================================================

private
  -- Optional whitespace, parser zero-or-more.  Canonical emit `[]`.
  withWSOpt : ∀ {A} → Format A → Format A
  withWSOpt f = iso proj₂ (λ a → tt , a) (λ _ → refl) (pair wsOpt f)

  -- Mandatory single space, parser one-or-more.  Canonical emit `' ' ∷ []`.
  withWS : ∀ {A} → Format A → Format A
  withWS f = iso proj₂ (λ a → tt , a) (λ _ → refl) (pair ws f)

  -- Canonical single space, parser zero-or-more.  Canonical emit
  -- `' ' ∷ []`.  Used for permissive whitespace slots that emit a
  -- single space when round-tripped (NS_ header `:` separator).
  withWSCanonOne : ∀ {A} → Format A → Format A
  withWSCanonOne f =
    iso proj₂ (λ a → tt , a) (λ _ → refl) (pair wsCanonOne f)

  -- Mandatory single tab, parser one-or-more isHSpace.  Canonical emit
  -- `'\t' ∷ []`.  Used for the NS_ keyword-line indent.
  withWSCanonTab : ∀ {A} → Format A → Format A
  withWSCanonTab f =
    iso proj₂ (λ a → tt , a) (λ _ → refl) (pair wsCanonTab f)

  -- Line terminator: accepts `"\r\n"` or `"\n"`, canonical emit `"\n"`.
  newlineFmt : Format ⊤
  newlineFmt = iso (λ _ → tt) (λ _ → inj₂ tt) (λ _ → refl)
                    (altSum (literal ('\r' ∷ '\n' ∷ []))
                            (literal ('\n' ∷ [])))

-- ============================================================================
-- VERSION FORMAT
-- ============================================================================

-- `"VERSION " <string-lit> <newline>`.  Carrier `List Char` (the body
-- chars of the string literal).  Outer iso flattens the underlying
-- pair tower `(List Char × ⊤)` to `List Char`.  Inline lambdas (rather
-- than where-bound helpers) keep the iso transparent to definitional
-- reduction at consumer call sites.
versionFmt : Format (List Char)
versionFmt =
  iso proj₁ (λ cs → cs , tt) (λ _ → refl) (
    withPrefix (toList "VERSION") (
     withWS (
      pair stringLit
       newlineFmt)))

-- VersionStop precondition is vacuous (the trailing newline is bare,
-- the next slot is consumed by the wrapper's `many parseNewline`).
-- No identifier or hspace context to discharge.

-- Build EmitsOK versionFmt v outer-suffix.  Reduces to a tower of
-- (vacuous, vacuous, ..., refl-disjointness) — every slot has a closed
-- head and either no precondition or `∷-stop refl` on a fixed char.
build-emits-ok-versionFmt :
    ∀ (v : List Char) (outer-suffix : List Char)
  → EmitsOK versionFmt v outer-suffix
build-emits-ok-versionFmt v outer-suffix =
  -- "VERSION" literal: vacuous.
  tt ,
  -- ws (mandatory single space): SuffixStops isHSpace on
  -- (quoteStringLit-chars v ++ '\n' ∷ outer-suffix).  The first char
  -- of `quoteStringLit-chars` is `'"'`, not hspace.
  ∷-stop refl ,
  -- stringLit: SuffixStops (λ c → c ≈ᵇ '"') on '\n' ∷ outer-suffix.
  ∷-stop refl ,
  -- newlineFmt's altSum inj₂ branch: literal "\n" vacuous + parse "\r\n"
  -- disjointness on '\n' ∷ outer-suffix (closes by λ _ → refl).
  tt ,
  λ _ → refl

-- Bridge: DSL emit ≡ existing formatter (with displaced trailing `'\n'`).
-- `emit versionFmt v` reduces to `toList "VERSION" ++ ' ' ∷
-- (quoteStringLit-chars v ++ '\n' ∷ [])` via iso/withPrefix/withWS/pair
-- unfolding.  Adding outer `'\n' ∷ []` and one `++ₗ-assoc` collapses to
-- `toList "VERSION " ++ quoteStringLit-chars v ++ toList "\n\n"`.
emit-versionFmt-eq-emitVersion-chars-prefix : ∀ (v : List Char)
  → emit versionFmt v ++ₗ '\n' ∷ [] ≡ emitVersion-chars v
emit-versionFmt-eq-emitVersion-chars-prefix v =
  trans (++ₗ-assoc (toList "VERSION ")
                    (quoteStringLit-chars v ++ₗ '\n' ∷ [])
                    ('\n' ∷ []))
   (cong (toList "VERSION " ++ₗ_)
     (++ₗ-assoc (quoteStringLit-chars v) ('\n' ∷ []) ('\n' ∷ [])))

-- Universal Format-roundtrip lemma: one-liner over `roundtrip versionFmt`
-- + `build-emits-ok-versionFmt`.  Used by the slim `parseVersion-
-- roundtrip` in `Properties/Preamble/Version.agda`.
parseVersion-format-roundtrip :
    ∀ (pos : Position) (v : List Char) (outer-suffix : List Char)
  → parse versionFmt pos (emit versionFmt v ++ₗ outer-suffix)
    ≡ just (mkResult v
             (advancePositions pos (emit versionFmt v))
             outer-suffix)
parseVersion-format-roundtrip pos v outer-suffix =
  roundtrip versionFmt pos v outer-suffix
    (build-emits-ok-versionFmt v outer-suffix)

-- ============================================================================
-- BS_ FORMAT
-- ============================================================================

-- `"BS_" <wsOpt> ":" <nonNewlineRun> <newline>`.  Carrier `⊤` (the bit
-- timing body is opaque).  Outer iso flattens `(⊤ × ⊤)` to `⊤`.
bitTimingFmt : Format ⊤
bitTimingFmt =
  iso (λ _ → tt) (λ _ → tt , tt) (λ _ → refl) (
    withPrefix (toList "BS_") (
     withWSOpt (
      withPrefix (':' ∷ []) (
       pair nonNewlineRun
        newlineFmt))))

-- Build EmitsOK bitTimingFmt tt outer-suffix.  Reduces structurally;
-- every SuffixStops obligation is on a fixed closed-head input.
build-emits-ok-bitTimingFmt :
    ∀ (outer-suffix : List Char)
  → EmitsOK bitTimingFmt tt outer-suffix
build-emits-ok-bitTimingFmt outer-suffix =
  -- "BS_" literal: vacuous.
  tt ,
  -- wsOpt: SuffixStops isHSpace on (':' ∷ '\n' ∷ outer-suffix).
  ∷-stop refl ,
  -- ":" literal: vacuous.
  tt ,
  -- nonNewlineRun: SuffixStops isNonNewline on '\n' ∷ outer-suffix.
  ∷-stop refl ,
  -- newlineFmt's altSum inj₂ branch: literal "\n" vacuous + disjointness.
  tt ,
  λ _ → refl

-- Bridge: `emit bitTimingFmt tt ++ '\n' ∷ [] ≡ emitBitTiming-chars`.
-- `emit bitTimingFmt tt` reduces to `toList "BS_:\n"` definitionally
-- (every leaf has a closed emit; the iso/withPrefix/withWSOpt all
-- project ⊤).  Adding the displaced trailing `'\n'` gives `BS_:\n\n`.
emit-bitTimingFmt-eq-emitBitTiming-chars-prefix :
  emit bitTimingFmt tt ++ₗ '\n' ∷ [] ≡ emitBitTiming-chars
emit-bitTimingFmt-eq-emitBitTiming-chars-prefix = refl

parseBitTiming-format-roundtrip :
    ∀ (pos : Position) (outer-suffix : List Char)
  → parse bitTimingFmt pos (emit bitTimingFmt tt ++ₗ outer-suffix)
    ≡ just (mkResult tt
             (advancePositions pos (emit bitTimingFmt tt))
             outer-suffix)
parseBitTiming-format-roundtrip pos outer-suffix =
  roundtrip bitTimingFmt pos tt outer-suffix
    (build-emits-ok-bitTimingFmt outer-suffix)

-- ============================================================================
-- NS_ FORMAT — discard-iso over `many nsLineFmt`
-- ============================================================================

-- One body line is either a blank (`\n`) or an indented keyword
-- (`\t<ident>\n`).  Each iteration of the body's `many nsLineFmt`
-- consumes one such line.
data NSLineShape : Set where
  ns-blank   : NSLineShape
  ns-keyword : Identifier → NSLineShape

-- Blank line: just `newlineFmt`.  Carrier ⊤.
private
  blankLineFmt : Format ⊤
  blankLineFmt = newlineFmt

  -- Keyword line: `'\t'` (mandatory hspace, canonical tab) + identifier
  -- + zero-or-more hspace + newline.  Carrier `Identifier` — iso
  -- projects out the inner identifier slot.  Inline lambdas (rather
  -- than where-bound helpers) keep the iso transparent to definitional
  -- reduction.
  keywordLineFmt : Format Identifier
  keywordLineFmt =
    iso proj₁ (λ i → i , tt) (λ _ → refl) (
     withWSCanonTab (
      pair ident (
       withWSOpt newlineFmt)))

-- iso helpers for nsLineFmt.  Module-level (not where-bound) so
-- definitional reduction is transparent at consumer call sites.
private
  ns-line-fwd : ⊤ ⊎ Identifier → NSLineShape
  ns-line-fwd (inj₁ _) = ns-blank
  ns-line-fwd (inj₂ i) = ns-keyword i

  ns-line-bwd : NSLineShape → ⊤ ⊎ Identifier
  ns-line-bwd ns-blank        = inj₁ tt
  ns-line-bwd (ns-keyword i)  = inj₂ i

  ns-line-inv : ∀ ns → ns-line-fwd (ns-line-bwd ns) ≡ ns
  ns-line-inv ns-blank        = refl
  ns-line-inv (ns-keyword _)  = refl

-- One body line — `altSum` over the two alternatives, dispatched via
-- iso to/from `NSLineShape`.
nsLineFmt : Format NSLineShape
nsLineFmt =
  iso ns-line-fwd ns-line-bwd ns-line-inv
      (altSum blankLineFmt keywordLineFmt)

-- ============================================================================
-- isNSLineStart precondition
-- ============================================================================

-- Re-export from `Properties.Preamble.Newline`-paired shape.  A char
-- starts an NS_ line iff it's hspace (keyword indent) or a newline
-- (blank line).  The wrapper's outer-suffix must NOT start with such
-- a char so `many nsLineFmt` terminates instead of consuming it.
isNSLineStart : Char → Bool
isNSLineStart c = isHSpace c ∨ isNewlineStart c

private
  ∨-false-split : ∀ {a b : Bool}
    → (a ∨ b) ≡ false → (a ≡ false) × (b ≡ false)
  ∨-false-split {false} {false} _ = refl , refl

-- ============================================================================
-- Termination certificate: parse nsLineFmt fails at outer-suffix
-- ============================================================================

-- `parse blankLineFmt = parse newlineFmt` fails on a non-newline-led
-- suffix.  Both `<|>` branches fail on the closed-head input; the iso's
-- outer `>>=` propagates `nothing`.
private
  parse-blankLine-fail-on-stop : ∀ (pos : Position) (suffix : List Char)
    → SuffixStops isNewlineStart suffix
    → parse blankLineFmt pos suffix ≡ nothing
  parse-blankLine-fail-on-stop pos []         _         = refl
  parse-blankLine-fail-on-stop pos (c ∷ cs)   (∷-stop h) =
    bind-nothing
      ((inj₁ <$> parse (literal ('\r' ∷ '\n' ∷ []))) <|>
        (inj₂ <$> parse (literal ('\n' ∷ []))))
      _ pos (c ∷ cs) alt-fail
    where
      ≈LF : (c ≈ᵇ '\n') ≡ false
      ≈LF with ∨-false-split {c ≈ᵇ '\n'} {c ≈ᵇ '\r'} h
      ... | lf , _ = lf

      ≈CR : (c ≈ᵇ '\r') ≡ false
      ≈CR with ∨-false-split {c ≈ᵇ '\n'} {c ≈ᵇ '\r'} h
      ... | _ , cr = cr

      char-LF-fail : char '\n' pos (c ∷ cs) ≡ nothing
      char-LF-fail rewrite ≈LF = refl

      char-CR-fail : char '\r' pos (c ∷ cs) ≡ nothing
      char-CR-fail rewrite ≈CR = refl

      parse-CRLF-fail :
        parse (literal ('\r' ∷ '\n' ∷ [])) pos (c ∷ cs) ≡ nothing
      parse-CRLF-fail =
        bind-nothing (parseCharsSeq ('\r' ∷ '\n' ∷ []))
           (λ _ → pure tt)
           pos (c ∷ cs)
           (bind-nothing (char '\r')
              (λ x → parseCharsSeq ('\n' ∷ []) >>=
                     λ xs → pure (x ∷ xs))
              pos (c ∷ cs)
              char-CR-fail)

      parse-LF-fail :
        parse (literal ('\n' ∷ [])) pos (c ∷ cs) ≡ nothing
      parse-LF-fail =
        bind-nothing (parseCharsSeq ('\n' ∷ []))
           (λ _ → pure tt)
           pos (c ∷ cs)
           (bind-nothing (char '\n')
              (λ x → parseCharsSeq [] >>=
                     λ xs → pure (x ∷ xs))
              pos (c ∷ cs)
              char-LF-fail)

      left-fail :
        (inj₁ <$> parse (literal ('\r' ∷ '\n' ∷ [])))
          pos (c ∷ cs)
        ≡ nothing
      left-fail =
        map-nothing inj₁ (parse (literal ('\r' ∷ '\n' ∷ [])))
          pos (c ∷ cs) parse-CRLF-fail

      right-fail :
        (inj₂ <$> parse (literal ('\n' ∷ [])))
          pos (c ∷ cs)
        ≡ nothing
      right-fail =
        map-nothing inj₂ (parse (literal ('\n' ∷ [])))
          pos (c ∷ cs) parse-LF-fail

      alt-fail :
        ((inj₁ <$> parse (literal ('\r' ∷ '\n' ∷ []))) <|>
         (inj₂ <$> parse (literal ('\n' ∷ []))))
          pos (c ∷ cs)
        ≡ nothing
      alt-fail = trans (alt-right-nothing
                          (inj₁ <$> parse (literal ('\r' ∷ '\n' ∷ [])))
                          (inj₂ <$> parse (literal ('\n' ∷ [])))
                          pos (c ∷ cs)
                          left-fail)
                      right-fail

-- `parse keywordLineFmt` fails on a non-hspace-led suffix.  The first
-- leaf is `wsCanonTab` whose parse is `parseWS = some (satisfy isHSpace)`.
-- `some` fails on `(c ∷ cs)` when `isHSpace c ≡ false`; the failure
-- propagates through the outer `>>=` via `bind-nothing`.
private
  parse-keywordLine-fail-on-stop : ∀ (pos : Position) (suffix : List Char)
    → SuffixStops isHSpace suffix
    → parse keywordLineFmt pos suffix ≡ nothing
  parse-keywordLine-fail-on-stop pos [] _ = refl
  parse-keywordLine-fail-on-stop pos (c ∷ cs) (∷-stop h) =
    -- parse keywordLineFmt = parse (iso ...) = parse <inner> >>= ...
    -- parse <inner> starts with parseWS; satisfy isHSpace fails on c.
    bind-nothing
      (parse (withWSCanonTab (pair ident (withWSOpt newlineFmt))))
      _ pos (c ∷ cs)
      inner-fail
    where
      -- parseWS pos (c ∷ cs) ≡ nothing because satisfy isHSpace rejects c.
      ws-fail : parseWS pos (c ∷ cs) ≡ nothing
      ws-fail rewrite h = refl

      -- parse wsCanonTab pos (c ∷ cs) ≡ nothing — the >>= propagates
      -- parseWS's failure.
      wsCanonTab-fail : parse wsCanonTab pos (c ∷ cs) ≡ nothing
      wsCanonTab-fail =
        bind-nothing parseWS (λ _ → pure tt) pos (c ∷ cs) ws-fail

      -- parse (pair wsCanonTab Q) pos (c ∷ cs) ≡ nothing — propagates
      -- via the bind chain.
      pair-fail :
        parse (pair wsCanonTab (pair ident (withWSOpt newlineFmt)))
              pos (c ∷ cs)
        ≡ nothing
      pair-fail =
        bind-nothing (parse wsCanonTab) _ pos (c ∷ cs) wsCanonTab-fail

      -- parse (withWSCanonTab Q) is the iso-wrapped pair.  The iso's
      -- `>>= λ a → pure (φ a)` propagates nothing.
      inner-fail :
        parse (withWSCanonTab (pair ident (withWSOpt newlineFmt)))
              pos (c ∷ cs)
        ≡ nothing
      inner-fail =
        bind-nothing
          (parse (pair wsCanonTab (pair ident (withWSOpt newlineFmt))))
          _ pos (c ∷ cs) pair-fail

-- The full termination certificate: `parse nsLineFmt pos suffix ≡
-- nothing` under `SuffixStops isNSLineStart suffix`.  Composes the two
-- branch-failure lemmas via `<|>` fall-through and one outer
-- `bind-nothing`.
parse-nsLineFmt-fail-on-stop : ∀ (pos : Position) (suffix : List Char)
  → SuffixStops isNSLineStart suffix
  → parse nsLineFmt pos suffix ≡ nothing
parse-nsLineFmt-fail-on-stop pos [] _ = refl
parse-nsLineFmt-fail-on-stop pos (c ∷ cs) (∷-stop h)
  with ∨-false-split {isHSpace c} {isNewlineStart c} h
... | hs-false , nl-false =
  bind-nothing
    ((inj₁ <$> parse blankLineFmt) <|> (inj₂ <$> parse keywordLineFmt))
    _ pos (c ∷ cs)
    alt-both-fail
  where
    left-fail :
      (inj₁ <$> parse blankLineFmt) pos (c ∷ cs) ≡ nothing
    left-fail =
      map-nothing inj₁ (parse blankLineFmt) pos (c ∷ cs)
        (parse-blankLine-fail-on-stop pos (c ∷ cs) (∷-stop nl-false))

    right-fail :
      (inj₂ <$> parse keywordLineFmt) pos (c ∷ cs) ≡ nothing
    right-fail =
      map-nothing inj₂ (parse keywordLineFmt) pos (c ∷ cs)
        (parse-keywordLine-fail-on-stop pos (c ∷ cs) (∷-stop hs-false))

    alt-both-fail :
      ((inj₁ <$> parse blankLineFmt) <|>
       (inj₂ <$> parse keywordLineFmt))
        pos (c ∷ cs)
      ≡ nothing
    alt-both-fail =
      trans (alt-right-nothing
               (inj₁ <$> parse blankLineFmt)
               (inj₂ <$> parse keywordLineFmt)
               pos (c ∷ cs) left-fail)
            right-fail

-- ============================================================================
-- Canonical 25 NS_ keyword identifiers + the trailing blank
-- ============================================================================

-- Each `mkIdent (toList "kw") tt` typechecks because every NS_ keyword
-- reduces to `T (validIdentifierᵇ (toList "kw")) ≡ ⊤` on the closed
-- string (the same canary the pre-3d.5.d `_Scratch.agda` tracked).
private
  mkKwId : (kw : String) → {valid : T (validIdentifierᵇ (toList kw))}
         → Identifier
  mkKwId kw {valid} = mkIdent (toList kw) valid

  ns-keyword-ids : List Identifier
  ns-keyword-ids =
    mkKwId "NS_DESC_"          ∷
    mkKwId "CM_"               ∷
    mkKwId "BA_DEF_"           ∷
    mkKwId "BA_"               ∷
    mkKwId "VAL_"              ∷
    mkKwId "CAT_DEF_"          ∷
    mkKwId "CAT_"              ∷
    mkKwId "FILTER"            ∷
    mkKwId "BA_DEF_DEF_"       ∷
    mkKwId "EV_DATA_"          ∷
    mkKwId "ENVVAR_DATA_"      ∷
    mkKwId "SGTYPE_"           ∷
    mkKwId "SGTYPE_VAL_"       ∷
    mkKwId "BA_DEF_SGTYPE_"    ∷
    mkKwId "BA_SGTYPE_"        ∷
    mkKwId "SIG_TYPE_REF_"     ∷
    mkKwId "VAL_TABLE_"        ∷
    mkKwId "SIG_GROUP_"        ∷
    mkKwId "SIG_VALTYPE_"      ∷
    mkKwId "SIGTYPE_VALTYPE_"  ∷
    mkKwId "BO_TX_BU_"         ∷
    mkKwId "BA_DEF_REL_"       ∷
    mkKwId "BA_REL_"           ∷
    mkKwId "BA_SGTYPE_REL_"    ∷
    mkKwId "SG_MUL_VAL_"       ∷
    []

  -- The 26-element canonical body: 25 keyword lines + 1 trailing blank.
  canonical-NSLine : List NSLineShape
  canonical-NSLine = map ns-keyword ns-keyword-ids ++ₗ ns-blank ∷ []

-- ============================================================================
-- NS_ FORMAT — top level
-- ============================================================================

-- `"NS_" <wsCanonOne> ":" <newline> (<nsLine>)*`.  Carrier `⊤`
-- (parseNamespace returns nothing of structural value — DBC has no
-- namespace field).  Outer iso projects the inner pair tower's
-- `⊤ × List NSLineShape` to `⊤`, with the inverse producing the
-- canonical 26-element body.
nsFmt : Format ⊤
nsFmt =
  iso (λ _ → tt) (λ _ → tt , canonical-NSLine) (λ _ → refl) (
    withPrefix (toList "NS_") (
     withWSCanonOne (
      withPrefix (':' ∷ []) (
       pair newlineFmt
        (many nsLineFmt)))))

-- Build EmitsOK nsLineFmt for one keyword line.  Reduces to a
-- (SuffixStops isHSpace, vacuous, ∷-stop refl, ∷-stop refl, tt,
-- λ _ → refl) tower; the outermost obligation is on `kw-name ++ '\n'
-- ∷ rest`, which has the keyword's first char as head — `∷-stop refl`
-- because every canonical keyword starts with a letter.  All other
-- slots are on closed-head fixed chars.
--
-- Plus the altSum disjointness witness for the inj₂ branch:
-- `parse blankLineFmt pos ('\t' ∷ kw-name ++ '\n' ∷ rest) ≡ nothing`
-- — closes by `λ _ → refl` because parse newlineFmt rejects '\t'-led
-- input definitionally.
private
  EmitsOK-keyword-line : ∀ (kw : Identifier) (rest : List Char)
    → SuffixStops isHSpace
        ((Identifier.name kw ++ₗ '\n' ∷ []) ++ₗ rest)
    → EmitsOK nsLineFmt (ns-keyword kw) rest
  EmitsOK-keyword-line kw rest kw-head-stop =
    -- inj₂ keyword branch:
    --   EmitsOK keywordLineFmt kw rest
    --   × disjointness witness for blankLineFmt branch
    ( -- EmitsOK keywordLineFmt kw rest unfolds via iso/pair to:
      -- (1) wsCanonTab: SuffixStops isHSpace (kw-name ++ '\n' ∷ rest)
      kw-head-stop ,
      -- (2) ident: SuffixStops isIdentCont ('\n' ∷ rest)
      ∷-stop refl ,
      -- (3) wsOpt: SuffixStops isHSpace ('\n' ∷ rest)
      ∷-stop refl ,
      -- (4) newlineFmt: (vacuous, λ _ → refl).
      tt ,
      λ _ → refl
    ) ,
    -- altSum disjointness: parse blankLineFmt rejects '\t' ∷ ...
    λ _ → refl

  -- Build EmitsOK nsLineFmt for the trailing blank.  Trivial:
  -- altSum's inj₁ branch (no disjointness witness needed).
  EmitsOK-blank-line : ∀ (rest : List Char)
    → SuffixStops isNewlineStart rest
    → EmitsOK nsLineFmt ns-blank rest
  EmitsOK-blank-line rest _ = tt , λ _ → refl

-- Build EmitsOKMany nsLineFmt over (map ns-keyword kws ++ ns-blank ∷ [])
-- on a canonical-keyword input.  Each keyword's first char is a letter
-- (closed-head) so `∷-stop refl` discharges the SuffixStops obligation
-- definitionally; the recursive structure is the natural one over
-- `List Identifier`.
private
  build-EmitsOKMany-canonical-keywords :
      ∀ (kws : List Identifier) (outer-suffix : List Char)
    → All (λ kw → ∀ rest → SuffixStops isHSpace
                            ((Identifier.name kw ++ₗ '\n' ∷ []) ++ₗ rest)) kws
    → SuffixStops isNSLineStart outer-suffix
    → EmitsOKMany nsLineFmt
        (map ns-keyword kws ++ₗ ns-blank ∷ [])
        outer-suffix
  build-EmitsOKMany-canonical-keywords [] outer-suffix _ outer-stop =
    ∷-cons
      (EmitsOK-blank-line outer-suffix
        (proj₂ (isNSLineStart-suffix-splits outer-suffix outer-stop)))
      (s≤s z≤n)
      ([]-fails (λ pos →
        parse-nsLineFmt-fail-on-stop pos outer-suffix outer-stop))
    where
      isNSLineStart-suffix-splits : ∀ suffix
        → SuffixStops isNSLineStart suffix
        → SuffixStops isHSpace suffix × SuffixStops isNewlineStart suffix
      isNSLineStart-suffix-splits []       _          = []-stop , []-stop
      isNSLineStart-suffix-splits (c ∷ _)  (∷-stop h)
        with ∨-false-split {isHSpace c} {isNewlineStart c} h
      ... | hs , nl = ∷-stop hs , ∷-stop nl
  build-EmitsOKMany-canonical-keywords (kw ∷ kws) outer-suffix
    (kw-stop All.∷ rest-stops) outer-stop =
    ∷-cons
      (EmitsOK-keyword-line kw
        (emit (many nsLineFmt) (map ns-keyword kws ++ₗ ns-blank ∷ [])
         ++ₗ outer-suffix)
        (kw-stop _))
      (s≤s z≤n)
      (build-EmitsOKMany-canonical-keywords kws outer-suffix
        rest-stops outer-stop)

-- The 25 per-keyword head-stops, supplied as 25 `λ _ → ∷-stop refl`
-- witnesses.  Every canonical keyword's first char is a letter, which
-- is not hspace; for any `rest`, `Identifier.name kw ++ '\n' ∷ rest`
-- has the same head as `Identifier.name kw`, so `∷-stop refl`
-- discharges the SuffixStops obligation definitionally.
private
  ns-keyword-ids-head-stops :
    All (λ kw → ∀ rest → SuffixStops isHSpace
                          ((Identifier.name kw ++ₗ '\n' ∷ []) ++ₗ rest))
        ns-keyword-ids
  ns-keyword-ids-head-stops =
    (λ _ → ∷-stop refl) All.∷ (λ _ → ∷-stop refl) All.∷
    (λ _ → ∷-stop refl) All.∷ (λ _ → ∷-stop refl) All.∷
    (λ _ → ∷-stop refl) All.∷ (λ _ → ∷-stop refl) All.∷
    (λ _ → ∷-stop refl) All.∷ (λ _ → ∷-stop refl) All.∷
    (λ _ → ∷-stop refl) All.∷ (λ _ → ∷-stop refl) All.∷
    (λ _ → ∷-stop refl) All.∷ (λ _ → ∷-stop refl) All.∷
    (λ _ → ∷-stop refl) All.∷ (λ _ → ∷-stop refl) All.∷
    (λ _ → ∷-stop refl) All.∷ (λ _ → ∷-stop refl) All.∷
    (λ _ → ∷-stop refl) All.∷ (λ _ → ∷-stop refl) All.∷
    (λ _ → ∷-stop refl) All.∷ (λ _ → ∷-stop refl) All.∷
    (λ _ → ∷-stop refl) All.∷ (λ _ → ∷-stop refl) All.∷
    (λ _ → ∷-stop refl) All.∷ (λ _ → ∷-stop refl) All.∷
    (λ _ → ∷-stop refl) All.∷
    All.[]

-- Build EmitsOK nsFmt tt outer-suffix.  Reduces structurally through
-- the outer iso and the four `withPrefix`/`withWS`/`withPrefix` slots
-- to a tower of (vacuous, ∷-stop refl, vacuous, vacuous + λ _ → refl,
-- EmitsOKMany over canonical-NSLine).
build-emits-ok-nsFmt : ∀ (outer-suffix : List Char)
  → SuffixStops isNSLineStart outer-suffix
  → EmitsOK nsFmt tt outer-suffix
build-emits-ok-nsFmt outer-suffix outer-stop =
  -- "NS_" literal: vacuous.
  tt ,
  -- wsCanonOne (zero-or-more, canonical single space):
  -- SuffixStops isHSpace (':' ∷ ...).
  ∷-stop refl ,
  -- ":" literal: vacuous.
  tt ,
  -- newlineFmt: (vacuous, λ _ → refl).
  ( tt , (λ _ → refl) ) ,
  -- many nsLineFmt over canonical-NSLine.
  build-EmitsOKMany-canonical-keywords ns-keyword-ids outer-suffix
    ns-keyword-ids-head-stops outer-stop

-- Universal Format-roundtrip lemma: one-liner over `roundtrip nsFmt`
-- + `build-emits-ok-nsFmt`.  Used by the slim `parseNamespace-
-- roundtrip` in `Properties/Preamble/Namespace.agda`.
parseNamespace-format-roundtrip :
    ∀ (pos : Position) (outer-suffix : List Char)
  → SuffixStops isNSLineStart outer-suffix
  → parse nsFmt pos (emit nsFmt tt ++ₗ outer-suffix)
    ≡ just (mkResult tt
             (advancePositions pos (emit nsFmt tt))
             outer-suffix)
parseNamespace-format-roundtrip pos outer-suffix outer-stop =
  roundtrip nsFmt pos tt outer-suffix
    (build-emits-ok-nsFmt outer-suffix outer-stop)

-- Bridge: `emit nsFmt tt ≡ emitNamespace-chars`.  The DSL captures the
-- entire 27-newline block (header `"NS_ :\n"` + 25 keyword lines + 1
-- trailing blank); reduction is definitional because every leaf has a
-- closed emit and the iso/withPrefix/many all unfold structurally.
emit-nsFmt-eq-emitNamespace-chars : emit nsFmt tt ≡ emitNamespace-chars
emit-nsFmt-eq-emitNamespace-chars = refl
