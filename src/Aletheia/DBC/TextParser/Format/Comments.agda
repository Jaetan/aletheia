{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.5.d — DSL-side `commentFmt` for the DBC `CM_` line.
--
-- Grammar slice (mirrors `TextParser.Comments.parseComment`):
--   comment        ::= "CM_" ws (comment-target)? ws? string-lit
--                      ws? ";" newline
--   comment-target ::= "BU_" ws ident ws            (CTNode)
--                    | "BO_" ws nat   ws            (CTMessage; raw ℕ)
--                    | "SG_" ws nat   ws ident ws   (CTSignal;  raw ℕ × ident)
--                    | "EV_" ws ident ws            (CTEnvVar)
--                    | (empty)                      (CTNetwork)
--
-- Raw-ℕ-in-Format precedent: 3d.8 `messageHeaderFmt : Format (ℕ × Identifier
-- × ℕ × Identifier)` keeps the CAN-ID as raw ℕ; the wrapper
-- (`buildCommentP`, in `TextParser.Comments`) lifts to `CANId` via
-- `buildCANId` and fails on out-of-range IDs.  Behaviour preserved: an
-- invalid CAN-ID under existing `parseComment` causes
-- `parseStringLit`-after-backtrack to fail on the leftover keyword (via
-- `<|>`'s reset-on-nothing semantics); under the migrated wrapper, the
-- partial `buildComment` returns `nothing` directly.  Both paths reject
-- the whole `parseComment` invocation.
--
-- The 5-way dispatch uses `altSum` left-associated:
--     ((((BU <|> BO) <|> SG) <|> EV) <|> Network)
-- with `Network = literal []` (empty emit, parser zero-consumption).
-- Each keyword leaf consumes its own trailing space so the carrier seam
-- between target and string-lit emits exactly one space (matching the
-- formatter's `body (CTNode n) = "CM_ BU_ " ++ name ++ ' ' ∷ quoted …`
-- shape — the per-target trailing space is part of the target slice, not
-- the post-target seam).
--
-- The trailing `many parseNewline` consumption (zero-or-more blank lines
-- after the line terminator) lives in the wrapper, NOT in this Format —
-- same pattern as `Format/ValueTable.agda` / `Format/EnvVar.agda`.
-- Formatter emits exactly one `\n`, captured by `newlineFmt` here.
module Aletheia.DBC.TextParser.Format.Comments where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char; _≈ᵇ_)
open import Data.List using (List; []; _∷_) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; Σ-syntax)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst)

open import Aletheia.Parser.Combinators
  using (Position; Parser; ParseResult; mkResult; advancePositions)
open import Aletheia.DBC.Identifier using (Identifier; isIdentCont)
open import Aletheia.DBC.Types
  using (CommentTarget; CTNetwork; CTNode; CTMessage; CTSignal; CTEnvVar;
         DBCComment; mkComment)
open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.DBC.TextParser.Lexer using (isHSpace)
open import Aletheia.DBC.TextFormatter.Emitter
  using (digitChar; showℕ-dec-chars; quoteStringLit-chars)
open import Aletheia.DBC.TextFormatter.Topology using (rawCanIdℕ)
open import Aletheia.DBC.TextParser.DecRatParse.Properties
  using (SuffixStops; ∷-stop; showNat-chars-head)
open import Aletheia.DBC.TextParser.Properties.Primitives
  using (quoteStringLit-chars-shape)
open import Aletheia.DBC.TextParser.Format
  using (Format; literal; ident; nat; stringLit; pair; iso; altSum;
         wsOpt; ws; withPrefix;
         emit; parse; EmitsOK;
         roundtrip)

-- ============================================================================
-- LOCAL SUGAR — ws-aware combinators (mirrors `Format.EnvVar`)
-- ============================================================================

private
  -- Mandatory single space, parser one-or-more.  Canonical emit `' ' ∷ []`.
  withWS : ∀ {A} → Format A → Format A
  withWS f = iso proj₂ (λ a → tt , a) (λ _ → refl) (pair ws f)

  -- Optional whitespace, parser zero-or-more.  Canonical emit `[]`.
  withWSOpt : ∀ {A} → Format A → Format A
  withWSOpt f = iso proj₂ (λ a → tt , a) (λ _ → refl) (pair wsOpt f)

  -- Trailing space after `f`.  Canonical emit `<emit f> ++ ' ' ∷ []`,
  -- parser one-or-more.  Matches the per-target trailing-`parseWS`
  -- convention from `Aletheia.DBC.TextParser.Comments` — every keyword
  -- target's last step is a `parseWS` whose canonical emit is the single
  -- space between the target and the string-lit `"`.
  withWSAfter : ∀ {A} → Format A → Format A
  withWSAfter f = iso proj₁ (λ a → a , tt) (λ _ → refl) (pair f ws)

  -- Line terminator: accepts `"\r\n"` or `"\n"`, canonical emit `"\n"`.
  newlineFmt : Format ⊤
  newlineFmt = iso (λ _ → tt) (λ _ → inj₂ tt) (λ _ → refl)
                    (altSum (literal ('\r' ∷ '\n' ∷ []))
                            (literal ('\n' ∷ [])))

-- ============================================================================
-- RAW COMMENT TARGET — Format intermediary; `buildComment` lifts to CANId
-- ============================================================================

-- Mirrors `CommentTarget` but with raw ℕ for CAN-IDs.  The Format produces
-- this intermediate; the wrapper `buildCommentP` in `TextParser.Comments`
-- runs `buildCANId` on the raw ℕ to recover the real `CANId`, failing on
-- out-of-range IDs.  Same precedent as 3d.8's `(rawId , msgName , rawDlc ,
-- msgSender)` carrier of `messageHeaderFmt`.
data RawCommentTarget : Set where
  RawCTNet  : RawCommentTarget
  RawCTNode : Identifier → RawCommentTarget
  RawCTMsg  : ℕ → RawCommentTarget
  RawCTSig  : ℕ → Identifier → RawCommentTarget
  RawCTEnv  : Identifier → RawCommentTarget

-- Project a `DBCComment.target` to its raw-ℕ-form.  `rawCanIdℕ` lifts
-- `CANId` to ℕ for the `CTMessage`/`CTSignal` arms.
rawTargetOf : CommentTarget → RawCommentTarget
rawTargetOf CTNetwork      = RawCTNet
rawTargetOf (CTNode n)     = RawCTNode n
rawTargetOf (CTMessage c)  = RawCTMsg (rawCanIdℕ c)
rawTargetOf (CTSignal c s) = RawCTSig (rawCanIdℕ c) s
rawTargetOf (CTEnvVar ev)  = RawCTEnv ev

-- ============================================================================
-- TARGET LEAF FORMATS — one per keyword + the network/empty case
-- ============================================================================

private
  -- "BU_ <ident> "  — `withPrefix "BU_"` then `withWS ident` then trailing
  -- space via `withWSAfter`.  Carrier collapses to `Identifier`.
  buNodeFmt : Format Identifier
  buNodeFmt = withPrefix (toList "BU_") (withWS (withWSAfter ident))

  -- "BO_ <nat> " — same shape with `nat` and ℕ carrier.
  boMsgFmt : Format ℕ
  boMsgFmt = withPrefix (toList "BO_") (withWS (withWSAfter nat))

  -- "SG_ <nat> <ident> " — three captures: nat, ident, then a trailing
  -- space.  Carrier `(ℕ × Identifier)` after flattening the trailing ⊤.
  sgSigFmt : Format (ℕ × Identifier)
  sgSigFmt =
    withPrefix (toList "SG_") (
      withWS (
        pair nat (
          withWS (
            withWSAfter ident))))

  -- "EV_ <ident> " — same shape as buNodeFmt with EV_ keyword.
  evVarFmt : Format Identifier
  evVarFmt = withPrefix (toList "EV_") (withWS (withWSAfter ident))

  -- Empty / network case.  `literal []` parses zero chars (always
  -- succeeds) and emits zero chars.  The carrier is `⊤`.
  netFmt : Format ⊤
  netFmt = literal []

-- ============================================================================
-- COMMENT TARGET FORMAT — left-associated 5-way altSum + iso
-- ============================================================================

-- Inner sum carrier matches the left-associated `altSum` nesting:
--     ((((Identifier ⊎ ℕ) ⊎ (ℕ × Identifier)) ⊎ Identifier) ⊎ ⊤)
-- The left arm always has one of the keyword targets; `inj₂ tt` is the
-- network-empty case.  altSum is left-biased, so the four keyword
-- alternatives are tried before the empty-emit network arm — matching
-- the existing `parseCommentTarget <|> pure CTNetwork` order.
private
  TargetCarrier : Set
  TargetCarrier =
    ((((Identifier ⊎ ℕ) ⊎ (ℕ × Identifier)) ⊎ Identifier) ⊎ ⊤)

  -- The 4-keyword left arm.  Used for the Network case's altSum
  -- disjointness witness.
  keywordTree : Format ((((Identifier ⊎ ℕ) ⊎ (ℕ × Identifier)) ⊎ Identifier))
  keywordTree =
    altSum (altSum (altSum buNodeFmt boMsgFmt) sgSigFmt) evVarFmt

  innerTargetFmt : Format TargetCarrier
  innerTargetFmt = altSum keywordTree netFmt

  fwdTgt : TargetCarrier → RawCommentTarget
  fwdTgt (inj₁ (inj₁ (inj₁ (inj₁ n))))    = RawCTNode n
  fwdTgt (inj₁ (inj₁ (inj₁ (inj₂ r))))    = RawCTMsg r
  fwdTgt (inj₁ (inj₁ (inj₂ (r , s))))     = RawCTSig r s
  fwdTgt (inj₁ (inj₂ ev))                  = RawCTEnv ev
  fwdTgt (inj₂ tt)                         = RawCTNet

  bwdTgt : RawCommentTarget → TargetCarrier
  bwdTgt RawCTNet       = inj₂ tt
  bwdTgt (RawCTNode n)  = inj₁ (inj₁ (inj₁ (inj₁ n)))
  bwdTgt (RawCTMsg r)   = inj₁ (inj₁ (inj₁ (inj₂ r)))
  bwdTgt (RawCTSig r s) = inj₁ (inj₁ (inj₂ (r , s)))
  bwdTgt (RawCTEnv ev)  = inj₁ (inj₂ ev)

  fwdTgt-bwdTgt : ∀ rt → fwdTgt (bwdTgt rt) ≡ rt
  fwdTgt-bwdTgt RawCTNet       = refl
  fwdTgt-bwdTgt (RawCTNode _)  = refl
  fwdTgt-bwdTgt (RawCTMsg _)   = refl
  fwdTgt-bwdTgt (RawCTSig _ _) = refl
  fwdTgt-bwdTgt (RawCTEnv _)   = refl

commentTargetFmt : Format RawCommentTarget
commentTargetFmt = iso fwdTgt bwdTgt fwdTgt-bwdTgt innerTargetFmt

-- ============================================================================
-- COMMENT FORMAT
-- ============================================================================

-- Underlying carrier: `RawCommentTarget × (List Char × ⊤)`.  The trailing
-- `⊤` is the result of the `wsOpt; literal ";"; newline` chain.  The
-- wrapper (`buildCommentP`, in `TextParser.Comments`) extracts
-- `(RawCommentTarget , List Char)` via `proj₁` / `proj₁ ∘ proj₂` —
-- avoiding the outer iso whose `bwd` was not reducing eagerly enough at
-- the per-rt EmitsOK slot's expected type.
CommentCarrier : Set
CommentCarrier = RawCommentTarget × (List Char × ⊤)

-- The full `CM_` line including the mandatory line-terminating `\n`.
-- The carrier `RawCommentTarget × (List Char × ⊤)` is the natural shape
-- of the underlying `pair` tower — no outer iso wrapping.
commentFmt : Format CommentCarrier
commentFmt =
  withPrefix (toList "CM_") (
    withWS (
      pair commentTargetFmt (
        pair stringLit (
          withWSOpt (
            withPrefix (';' ∷ []) newlineFmt)))))

-- ============================================================================
-- PER-TARGET PRECONDITION — `NameStop` lifted to DBCComment level
-- ============================================================================

-- Each Identifier-bearing target arm requires `Identifier.name`
-- decomposes as `c ∷ cs` with `isHSpace c ≡ false`.  Layer 4 will
-- discharge this universally from `validIdentifierᵇ` via the
-- `isIdentStart→¬isHSpace` bridge (see
-- `project_b3d_layer4_owed_lemmas.md`).
NameStop : Identifier → Set
NameStop n =
  Σ[ c ∈ Char ] Σ[ cs ∈ List Char ]
    (Identifier.name n ≡ c ∷ cs) × (isHSpace c ≡ false)

-- Per-RawCommentTarget precondition: per-name witnesses for the
-- Identifier-bearing constructors only.
TgtStop : RawCommentTarget → Set
TgtStop RawCTNet       = ⊤
TgtStop (RawCTNode n)  = NameStop n
TgtStop (RawCTMsg _)   = ⊤
TgtStop (RawCTSig _ s) = NameStop s
TgtStop (RawCTEnv ev)  = NameStop ev

-- DBCComment-level precondition: project per-target name witnesses.
-- Network and Message targets carry no per-name witness (no Identifier).
CommentTargetStop : DBCComment → Set
CommentTargetStop c with DBCComment.target c
... | CTNetwork    = ⊤
... | CTNode n     = NameStop n
... | CTMessage _  = ⊤
... | CTSignal _ s = NameStop s
... | CTEnvVar ev  = NameStop ev

-- ============================================================================
-- PRIVATE HELPERS — head-class reductions on emitted heads
-- ============================================================================

private
  -- `digitChar d` is non-hspace for every closed `d` (10-case +
  -- fall-through).  Used to bridge `nat` digit emits to the next
  -- ws/non-ws boundary in `boMsgFmt`/`sgSigFmt`.
  digitChar-not-isHSpace : ∀ d → isHSpace (digitChar d) ≡ false
  digitChar-not-isHSpace 0 = refl
  digitChar-not-isHSpace 1 = refl
  digitChar-not-isHSpace 2 = refl
  digitChar-not-isHSpace 3 = refl
  digitChar-not-isHSpace 4 = refl
  digitChar-not-isHSpace 5 = refl
  digitChar-not-isHSpace 6 = refl
  digitChar-not-isHSpace 7 = refl
  digitChar-not-isHSpace 8 = refl
  digitChar-not-isHSpace 9 = refl
  digitChar-not-isHSpace
    (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc _)))))))))) = refl

  -- Head of `(showℕ-dec-chars n ++ inner-rest) ++ outer-suffix` is non-
  -- hspace for every ℕ.  Left-bracketed form matches the natural shape
  -- of `withWSAfter (pair nat …)` slots.
  showNat-chars-head-non-hspace : ∀ (n : ℕ) (inner-rest outer-suffix : List Char)
    → SuffixStops isHSpace
        ((showℕ-dec-chars n ++ₗ inner-rest) ++ₗ outer-suffix)
  showNat-chars-head-non-hspace n inner-rest outer-suffix
    with showNat-chars-head n
  ... | d , tail , _ , eq =
        subst (λ xs → SuffixStops isHSpace ((xs ++ₗ inner-rest) ++ₗ outer-suffix))
              (sym eq)
              (∷-stop (digitChar-not-isHSpace d))

  -- Name-decomposition lemma: from `NameStop n`, extract a non-hspace
  -- head for the `(name ++ inner-rest) ++ outer-suffix` shape.  Mirrors
  -- the pattern in `Format/Nodes.agda`.
  name-stop-non-hspace : ∀ (n : Identifier) (inner-rest outer-suffix : List Char)
    → NameStop n
    → SuffixStops isHSpace
        ((Identifier.name n ++ₗ inner-rest) ++ₗ outer-suffix)
  name-stop-non-hspace n inner-rest outer-suffix
                       (c , cs , name-eq , c-non-hs) =
    subst (λ xs → SuffixStops isHSpace ((xs ++ₗ inner-rest) ++ₗ outer-suffix))
          (sym name-eq)
          (∷-stop c-non-hs)

-- ============================================================================
-- QUOTE-PREFIXED OUTER-SUFFIX HELPERS
-- ============================================================================
--
-- The outer-suffix passed to `commentTargetFmt`'s slot in
-- `build-emits-ok` is `quoteStringLit-chars text ++ ';' ∷ '\n' ∷
-- outer-outer-suffix`.  Its head is `'"'` (via
-- `quoteStringLit-chars-shape`), which is (a) non-hspace (used for the
-- trailing-ws slot of each keyword leaf) and (b) not 'B'/'S'/'E' (used
-- for the Network case's altSum disjointness, since each keyword
-- parser's `string` matcher fails by closed-Char comparison on `'"'`).

private
  -- `SuffixStops isHSpace (quoteStringLit-chars text ++ rest)` —
  -- `quoteStringLit-chars text` definitionally reduces to `'"' ∷
  -- <foldr-body>` (single-clause definition), so the head of the full
  -- list is `'"'` (non-hspace).  `∷-stop refl` discharges directly
  -- without needing the shape lemma.
  quoted-head-stop : ∀ (text rest : List Char)
    → SuffixStops isHSpace (quoteStringLit-chars text ++ₗ rest)
  quoted-head-stop _ _ = ∷-stop refl

  -- Each keyword-leaf parser fails on input prefixed with
  -- `quoteStringLit-chars text`.  After substituting the head shape,
  -- `parse <leaf> pos ('"' ∷ <body>) ++ rest` reduces to `nothing`
  -- definitionally because `parseCharsSeq <keyword> pos ('"' ∷ ...)`
  -- fails on the leading-char comparison.
  buNodeFmt-fails-on-quoted : ∀ (text rest : List Char) (pos : Position)
    → parse buNodeFmt pos (quoteStringLit-chars text ++ₗ rest) ≡ nothing
  buNodeFmt-fails-on-quoted text rest pos =
    subst (λ xs → parse buNodeFmt pos (xs ++ₗ rest) ≡ nothing)
          (sym (quoteStringLit-chars-shape text))
          refl

  boMsgFmt-fails-on-quoted : ∀ (text rest : List Char) (pos : Position)
    → parse boMsgFmt pos (quoteStringLit-chars text ++ₗ rest) ≡ nothing
  boMsgFmt-fails-on-quoted text rest pos =
    subst (λ xs → parse boMsgFmt pos (xs ++ₗ rest) ≡ nothing)
          (sym (quoteStringLit-chars-shape text))
          refl

  sgSigFmt-fails-on-quoted : ∀ (text rest : List Char) (pos : Position)
    → parse sgSigFmt pos (quoteStringLit-chars text ++ₗ rest) ≡ nothing
  sgSigFmt-fails-on-quoted text rest pos =
    subst (λ xs → parse sgSigFmt pos (xs ++ₗ rest) ≡ nothing)
          (sym (quoteStringLit-chars-shape text))
          refl

  evVarFmt-fails-on-quoted : ∀ (text rest : List Char) (pos : Position)
    → parse evVarFmt pos (quoteStringLit-chars text ++ₗ rest) ≡ nothing
  evVarFmt-fails-on-quoted text rest pos =
    subst (λ xs → parse evVarFmt pos (xs ++ₗ rest) ≡ nothing)
          (sym (quoteStringLit-chars-shape text))
          refl

  -- `parse keywordTree pos (quoteStringLit-chars text ++ rest) ≡
  -- nothing` — composes the four leaf-failure proofs through the nested
  -- altSum tree.  Each `<|>` reduces to its right branch when the left
  -- returns `nothing`; recursing through 3 nested altSums lands the
  -- final-branch failure.
  keywordTree-fails-on-quoted : ∀ (text rest : List Char) (pos : Position)
    → parse keywordTree pos (quoteStringLit-chars text ++ₗ rest) ≡ nothing
  keywordTree-fails-on-quoted text rest pos =
    subst (λ xs → parse keywordTree pos (xs ++ₗ rest) ≡ nothing)
          (sym (quoteStringLit-chars-shape text))
          refl

-- ============================================================================
-- PER-LEAF EmitsOK BUILDERS — outer-suffix-stop precondition
-- ============================================================================

private
  -- `buNodeFmt`: emit "BU_" + " " + name + " ".  The 4-tuple matches
  -- the EmitsOK reduction: ⊤ × ws-slot1 × isIdentCont-slot × ws-slot2.
  -- The ws-slot2 (trailing-`withWSAfter`'s outer-suffix obligation) is
  -- the caller-supplied `outer-stop`.
  build-buNodeFmt-EmitsOK : ∀ (n : Identifier) (outer-suffix : List Char)
    → NameStop n
    → SuffixStops isHSpace outer-suffix
    → EmitsOK buNodeFmt n outer-suffix
  build-buNodeFmt-EmitsOK n outer-suffix nameStop outer-stop =
      tt
    , name-stop-non-hspace n (' ' ∷ []) outer-suffix nameStop
    , ∷-stop refl
    , outer-stop

  build-evVarFmt-EmitsOK : ∀ (ev : Identifier) (outer-suffix : List Char)
    → NameStop ev
    → SuffixStops isHSpace outer-suffix
    → EmitsOK evVarFmt ev outer-suffix
  build-evVarFmt-EmitsOK ev outer-suffix nameStop outer-stop =
      tt
    , name-stop-non-hspace ev (' ' ∷ []) outer-suffix nameStop
    , ∷-stop refl
    , outer-stop

  build-boMsgFmt-EmitsOK : ∀ (r : ℕ) (outer-suffix : List Char)
    → SuffixStops isHSpace outer-suffix
    → EmitsOK boMsgFmt r outer-suffix
  build-boMsgFmt-EmitsOK r outer-suffix outer-stop =
      tt
    , showNat-chars-head-non-hspace r (' ' ∷ []) outer-suffix
    , ∷-stop refl
    , outer-stop

  build-sgSigFmt-EmitsOK : ∀ (r : ℕ) (s : Identifier) (outer-suffix : List Char)
    → NameStop s
    → SuffixStops isHSpace outer-suffix
    → EmitsOK sgSigFmt (r , s) outer-suffix
  build-sgSigFmt-EmitsOK r s outer-suffix sigStop outer-stop =
      -- L1 (literal "SG_"): vacuous.
      tt
      -- L2 (outer withWS — ws between "SG_" and nat): SuffixStops isHSpace
      -- (showNat r ++ ' ' ∷ name ++ ' ' ∷ outer-suffix); head is showNat
      -- digit.
    , showNat-chars-head-non-hspace r
        (' ' ∷ Identifier.name s ++ₗ ' ' ∷ []) outer-suffix
      -- L3 (nat slot — SuffixStops isDigit): head of post-nat is ' ',
      -- non-digit.
    , ∷-stop refl
      -- L4 (inner withWS — ws between nat and ident): SuffixStops isHSpace
      -- ((name ++ ' ' ∷ []) ++ outer-suffix); head of name is non-hspace
      -- via NameStop.
    , name-stop-non-hspace s (' ' ∷ []) outer-suffix sigStop
      -- L5 (ident slot — SuffixStops isIdentCont): head of post-ident is
      -- ' ', non-isIdentCont.
    , ∷-stop refl
      -- L6 (trailing ws — withWSAfter): outer-suffix's head non-hspace.
    , outer-stop

-- ============================================================================
-- WELL-FORMEDNESS — top-level builder
-- ============================================================================

private
  -- Probe whether `emit (withWSOpt (withPrefix ";" newlineFmt)) tt`
  -- reduces to `';' ∷ '\n' ∷ []` definitionally.  If this lemma closes
  -- by `refl`, the call-site mismatches in `build-emits-ok` can be
  -- bridged by `subst` over this equation.
  emit-line-tail-eq :
      emit (withWSOpt (withPrefix (';' ∷ []) newlineFmt)) tt
      ≡ ';' ∷ '\n' ∷ []
  emit-line-tail-eq = refl

build-emits-ok : ∀ (c : DBCComment) (outer-suffix : List Char)
  → CommentTargetStop c
  → EmitsOK commentFmt
      (rawTargetOf (DBCComment.target c) , DBCComment.text c , tt)
      outer-suffix
-- ============================================================================
-- CTNetwork: emit commentTargetFmt RawCTNet = []; head of L2's argument
-- is '"' (from stringLit's leading quote).  The per-rt commentTargetFmt
-- slot returns `tt × keywordTree-disjointness-on-'"'-prefixed-input`.
-- ============================================================================
build-emits-ok (mkComment CTNetwork text) outer-suffix _ =
    tt                                                    -- L1
  , ∷-stop refl                                            -- L2: head '"'
  , (tt , λ pos → refl)                                    -- L3: ⊤ × disjointness
                                                            --   (parse keywordTree on input
                                                            --    starting with '"' fails by
                                                            --    closed-Char reduction)
  , ∷-stop refl                                            -- L4 stringLit ≈ᵇ '"'
  , ∷-stop refl                                            -- L5 wsOpt isHSpace
  , tt                                                     -- L6 literal ";"
  , tt                                                     -- L7 newlineFmt inj₂ inner
  , (λ _ → refl)                                           -- L8 newlineFmt disjointness
-- ============================================================================
-- CTNode n: emit commentTargetFmt = "BU_ <name> ".  Head 'B', non-hspace.
-- The per-rt slot uses build-buNodeFmt-EmitsOK; no altSum disjointness
-- (this is at inj₁ of every altSum level).
-- ============================================================================
build-emits-ok (mkComment (CTNode n) text) outer-suffix nameStop =
    tt
  , ∷-stop refl                                            -- L2: head 'B'
  , build-buNodeFmt-EmitsOK n
      (emit (pair stringLit (withWSOpt (withPrefix (';' ∷ []) newlineFmt)))
            (text , tt)
       ++ₗ outer-suffix)
      nameStop
      (∷-stop refl)
  , ∷-stop refl
  , ∷-stop refl
  , tt
  , tt
  , (λ _ → refl)
-- ============================================================================
-- CTMessage cid: emit commentTargetFmt = "BO_ <rawId> ".  Head 'B'.
-- Per-rt slot: build-boMsgFmt-EmitsOK + altSum disjointness against
-- buNodeFmt (parser fails on 'B' ∷ 'O' ∷ ... — second char 'U' vs 'O').
-- ============================================================================
build-emits-ok (mkComment (CTMessage cid) text) outer-suffix _ =
    tt
  , ∷-stop refl
  , (build-boMsgFmt-EmitsOK (rawCanIdℕ cid)
       (emit (pair stringLit (withWSOpt (withPrefix (';' ∷ []) newlineFmt)))
             (text , tt)
        ++ₗ outer-suffix)
       (∷-stop refl)
     , (λ _ → refl))
  , ∷-stop refl
  , ∷-stop refl
  , tt
  , tt
  , (λ _ → refl)
-- ============================================================================
-- CTSignal cid s: emit commentTargetFmt = "SG_ <rawId> <name> ".  Head
-- 'S'.  Per-rt slot: build-sgSigFmt-EmitsOK + altSum disjointness
-- against altSum buNodeFmt boMsgFmt (both BU_/BO_ leaves fail on 'S').
-- ============================================================================
build-emits-ok (mkComment (CTSignal cid s) text) outer-suffix sigStop =
    tt
  , ∷-stop refl
  , (build-sgSigFmt-EmitsOK (rawCanIdℕ cid) s
       (emit (pair stringLit (withWSOpt (withPrefix (';' ∷ []) newlineFmt)))
             (text , tt)
        ++ₗ outer-suffix)
       sigStop
       (∷-stop refl)
     , (λ _ → refl))
  , ∷-stop refl
  , ∷-stop refl
  , tt
  , tt
  , (λ _ → refl)
-- ============================================================================
-- CTEnvVar ev: emit commentTargetFmt = "EV_ <name> ".  Head 'E'.
-- Per-rt slot: build-evVarFmt-EmitsOK + altSum disjointness against
-- the 3-leaf inner tree (BU_/BO_/SG_ all fail on 'E').
-- ============================================================================
build-emits-ok (mkComment (CTEnvVar ev) text) outer-suffix evStop =
    tt
  , ∷-stop refl
  , (build-evVarFmt-EmitsOK ev
       (emit (pair stringLit (withWSOpt (withPrefix (';' ∷ []) newlineFmt)))
             (text , tt)
        ++ₗ outer-suffix)
       evStop
       (∷-stop refl)
     , (λ _ → refl))
  , ∷-stop refl
  , ∷-stop refl
  , tt
  , tt
  , (λ _ → refl)

-- ============================================================================
-- TOP-LEVEL ROUNDTRIP — the universal-form theorem
-- ============================================================================

-- THE GATE: parseComment's line-portion expressed via Format DSL.  Body is
-- one `roundtrip` call + the EmitsOK construction.  Universal in `c` and
-- `outer-suffix`; the only domain precondition is `CommentTargetStop c`,
-- which Layer 4 will discharge universally from `validIdentifierᵇ`.
parseComment-format-roundtrip :
    ∀ (pos : Position) (c : DBCComment) (outer-suffix : List Char)
  → CommentTargetStop c
  → parse commentFmt pos
      (emit commentFmt
            (rawTargetOf (DBCComment.target c) , DBCComment.text c , tt)
       ++ₗ outer-suffix)
    ≡ just (mkResult
             (rawTargetOf (DBCComment.target c) , DBCComment.text c , tt)
             (advancePositions pos
                (emit commentFmt
                  (rawTargetOf (DBCComment.target c) , DBCComment.text c , tt)))
             outer-suffix)
parseComment-format-roundtrip pos c outer-suffix tgtStop =
  roundtrip commentFmt pos
    (rawTargetOf (DBCComment.target c) , DBCComment.text c , tt)
    outer-suffix
    (build-emits-ok c outer-suffix tgtStop)
