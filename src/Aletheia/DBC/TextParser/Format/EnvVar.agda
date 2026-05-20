{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.5.d — DSL-side `envVarFmt` for the DBC `EV_` line.
--
-- The wire grammar carries 14 tokens (cantools `dbc.py:308-311` Sequence);
-- the Agda `EnvironmentVar` record retains 5 (name, varType, initial,
-- minimum, maximum).  Four wire-only tokens (unit, env_id, access_type,
-- access_node) are *parsed* (so ill-formed inputs reject the whole file)
-- and *emit* canonical placeholders that reparse cleanly: `""`, `0`,
-- `DUMMY_NODE_VECTOR0`, `Vector__XXX`.  The DSL captures this asymmetry
-- via a `discardFmt` sugar combinator built on `iso`.
--
-- Whitespace fidelity (production-permissive, canonical-emit):
--   * `withWS`        — eight mandatory single-space slots.
--   * `withWSOpt`     — two production-permissive zero-or-more slots
--                       (between name and `:`, between access_node and `;`);
--                       both have canonical empty emit.
--   * `newlineFmt`    — line terminator; canonical emit `'\n'`, parser
--                       accepts `'\n'` and `'\r\n'`.
--
-- The trailing `many parseNewline` consumption (zero-or-more blank lines
-- after the line terminator) lives in the wrapper, NOT in this Format —
-- same pattern as `Format/ValueTable.agda`: formatter emits exactly one
-- `\n` so the wrapper's `many parseNewline` consumes zero from suffix.
module Aletheia.DBC.TextParser.Format.EnvVar where

open import Data.Bool using (false)
open import Data.Char using (Char)
open import Data.Integer using (ℤ) renaming (+_ to ℤ+_; -[1+_] to ℤ-[1+_])
open import Data.List using (List; []; _∷_) renaming (_++_ to _++ₗ_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₂; Σ; Σ-syntax)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)

open import Aletheia.Parser.Combinators
  using (Position; Parser; mkResult; advancePositions)
open import Aletheia.DBC.Identifier using (Identifier; mkIdent; isIdentCont)
open import Aletheia.DBC.DecRat using (DecRat; mkDecRat)
open import Aletheia.DBC.Types
  using (EnvironmentVar; VarType; IntVar; FloatVar; StringVar)
open import Aletheia.DBC.TextParser.Lexer using (isHSpace)
open import Aletheia.DBC.TextFormatter.Emitter
  using (digitChar; showDecRat-dec-chars)
open import Aletheia.DBC.TextParser.DecRatParse.Properties
  using (SuffixStops; ∷-stop;
         showDecRat-chars-head-dash; showDecRat-chars-head-digit)
open import Aletheia.DBC.TextParser.Format
  using (Format; literal; ident; nat; stringLit; pair; iso; many;
         altSum; ws; wsOpt; decRat; withPrefix;
         emit; parse; EmitsOK;
         roundtrip)
open import Aletheia.DBC.TextParser.Properties.Attributes.Assign.Common
  using (digitChar-not-isHSpace)

-- ============================================================================
-- LOCAL SUGAR — ws-aware combinators (mirrors `Format.ValueTable` /
-- `Format.Nodes`)
-- ============================================================================

private
  -- Mandatory single space, parser one-or-more.  Canonical emit `' ' ∷ []`.
  withWS : ∀ {A} → Format A → Format A
  withWS f = iso proj₂ (λ a → tt , a) (λ _ → refl) (pair ws f)

  -- Optional whitespace, parser zero-or-more.  Canonical emit `[]`.
  withWSOpt : ∀ {A} → Format A → Format A
  withWSOpt f = iso proj₂ (λ a → tt , a) (λ _ → refl) (pair wsOpt f)

  -- Line terminator: accepts `"\r\n"` or `"\n"`, canonical emit `"\n"`.
  newlineFmt : Format ⊤
  newlineFmt = iso (λ _ → tt) (λ _ → inj₂ tt) (λ _ → refl)
                    (altSum (literal ('\r' ∷ '\n' ∷ []))
                            (literal ('\n' ∷ [])))

  -- Discard combinator: parse anything matching `f` (production-
  -- permissive), discard the result; emit `f`'s canonical default.
  -- Sugar over `iso`: `φ : A → ⊤` is `const tt`, `ψ : ⊤ → A` is
  -- `const default`, the `φ (ψ b) ≡ b` law holds trivially because
  -- `b : ⊤`.  Used for the 4 wire-only EV_ fields the Agda record drops.
  discardFmt : ∀ {A} → A → Format A → Format ⊤
  discardFmt default f =
    iso (λ _ → tt) (λ _ → default) (λ _ → refl) f

-- ============================================================================
-- VARTYPE FORMAT — 3-way altSum + iso
-- ============================================================================

-- `Format VarType` via altSum-tree of three single-char literals + iso to
-- the named ADT.  Mirrors the production parser's `(char '0' *> pure
-- IntVar) <|> (char '1' *> pure FloatVar) <|> (char '2' *> pure
-- StringVar)`.
varTypeFmt : Format VarType
varTypeFmt =
  iso fwd bwd fwd-bwd
    (altSum (literal ('0' ∷ []))
            (altSum (literal ('1' ∷ []))
                    (literal ('2' ∷ []))))
  where
    fwd : ⊤ ⊎ (⊤ ⊎ ⊤) → VarType
    fwd (inj₁ tt)        = IntVar
    fwd (inj₂ (inj₁ tt)) = FloatVar
    fwd (inj₂ (inj₂ tt)) = StringVar

    bwd : VarType → ⊤ ⊎ (⊤ ⊎ ⊤)
    bwd IntVar    = inj₁ tt
    bwd FloatVar  = inj₂ (inj₁ tt)
    bwd StringVar = inj₂ (inj₂ tt)

    fwd-bwd : ∀ b → fwd (bwd b) ≡ b
    fwd-bwd IntVar    = refl
    fwd-bwd FloatVar  = refl
    fwd-bwd StringVar = refl

-- Per-VarType `EmitsOK varTypeFmt vt suffix` builder.  Reduces structurally
-- through `iso → altSum`-tree per case.  Each disjointness witness closes
-- by `λ _ → refl` — the `parse (literal ['0'])` against `'1' ∷ …` /
-- `'2' ∷ …` reduces to `nothing` definitionally on the closed-char
-- mismatch.
build-EmitsOK-varTypeFmt : ∀ (vt : VarType) (suffix : List Char)
  → EmitsOK varTypeFmt vt suffix
build-EmitsOK-varTypeFmt IntVar    _ = tt
build-EmitsOK-varTypeFmt FloatVar  _ = tt , (λ _ → refl)
build-EmitsOK-varTypeFmt StringVar _ = (tt , (λ _ → refl)) , (λ _ → refl)

-- Head of `(emit varTypeFmt vt ++ inner-rest) ++ outer-suffix` is non-
-- hspace.  Each VarType emits exactly one closed digit (`'0'`/`'1'`/`'2'`).
-- Left-bracketed form matches the natural shape Agda's EmitsOK reduces
-- the `withWS (pair varTypeFmt …)` slot to.
emit-varTypeFmt-head-non-hspace : ∀ (vt : VarType)
                                    (inner-rest outer-suffix : List Char)
  → SuffixStops isHSpace
      ((emit varTypeFmt vt ++ₗ inner-rest) ++ₗ outer-suffix)
emit-varTypeFmt-head-non-hspace IntVar    _ _ = ∷-stop refl
emit-varTypeFmt-head-non-hspace FloatVar  _ _ = ∷-stop refl
emit-varTypeFmt-head-non-hspace StringVar _ _ = ∷-stop refl

-- ============================================================================
-- SYNTHESIZED PLACEHOLDER IDENTIFIERS
-- ============================================================================

-- The wire grammar's `access_type` and `access_node` slots demand
-- identifiers; the Agda record drops both.  These are the canonical
-- emit defaults (matching cantools' None-handling fallbacks).  Both
-- names' `validIdentifierᵇ`-ness reduces to `tt` definitionally on the
-- closed-Char path; the canary in
-- `Properties/EnvVars/_Scratch.agda` traps any stdlib regression.
ident-DummyNode : Identifier
ident-DummyNode = mkIdent (toList "DUMMY_NODE_VECTOR0") tt

ident-VectorXXX : Identifier
ident-VectorXXX = mkIdent (toList "Vector__XXX") tt

-- ============================================================================
-- ENVVAR FORMAT
-- ============================================================================

-- Inner-format carrier: tuple of all parsed pieces in wire order.
-- Wire-only fields (unit, env_id, access_type, access_node) collapse to
-- `⊤` via `discardFmt`; the trailing newline format also produces `⊤`.
-- Right-associative `_×_` (infixr 4) flattens the nested-pair structure
-- the underlying `pair`-tower produces.
private
  EnvVarInner : Set
  EnvVarInner =
    Identifier × VarType × DecRat × DecRat
      × ⊤ × DecRat × ⊤ × ⊤ × ⊤ × ⊤

-- The full `EV_` line including the mandatory line-terminating `\n`.
-- Outer iso converts between the underlying nested-pair carrier and the
-- user-facing `EnvironmentVar` record.  The `bwd ev` projection emits
-- with `tt`s in the wire-only slots; `fwd` reconstructs the record from
-- the projected fields, closing by record-η on `EnvironmentVar`.
envVarFmt : Format EnvironmentVar
envVarFmt =
  iso fwd bwd (λ _ → refl) inner
  where
    fwd : EnvVarInner → EnvironmentVar
    fwd (n , vt , mn , mx , _ , ini , _ , _ , _ , _) =
      record { name    = n
             ; varType = vt
             ; initial = ini
             ; minimum = mn
             ; maximum = mx
             }

    bwd : EnvironmentVar → EnvVarInner
    bwd ev =
        EnvironmentVar.name    ev
      , EnvironmentVar.varType ev
      , EnvironmentVar.minimum ev
      , EnvironmentVar.maximum ev
      , tt
      , EnvironmentVar.initial ev
      , tt , tt , tt , tt

    inner : Format EnvVarInner
    inner =
      withPrefix (toList "EV_") (
        withWS (
          pair ident (
            withWSOpt (
              withPrefix (':' ∷ []) (
                withWS (
                  pair varTypeFmt (
                    withWS (
                      withPrefix ('[' ∷ []) (
                        pair decRat (
                          withPrefix ('|' ∷ []) (
                            pair decRat (
                              withPrefix (']' ∷ []) (
                                withWS (
                                  pair (discardFmt [] stringLit) (
                                    withWS (
                                      pair decRat (
                                        withWS (
                                          pair (discardFmt 0 nat) (
                                            withWS (
                                              pair (discardFmt ident-DummyNode ident) (
                                                withWS (
                                                  pair (discardFmt ident-VectorXXX ident) (
                                                    withWSOpt (
                                                      withPrefix (';' ∷ []) newlineFmt
                                                    ))))))))))))))))))))))))

-- ============================================================================
-- PER-LINE PRECONDITION (mirrors η's `NameStop`)
-- ============================================================================

-- Each EV_ entry's `name` decomposes as `c ∷ cs` with `isHSpace c ≡
-- false`.  Layer 4 will discharge this universally from
-- `validIdentifierᵇ` via the `isIdentStart→¬isHSpace` bridge (see
-- `project_b3d_layer4_owed_lemmas.md`).
EnvVarNameStop : EnvironmentVar → Set
EnvVarNameStop ev =
  Σ[ c ∈ Char ] Σ[ cs ∈ List Char ]
    (Identifier.name (EnvironmentVar.name ev) ≡ c ∷ cs) × (isHSpace c ≡ false)

-- ============================================================================
-- PRIVATE HELPERS — head-class reductions on emitted heads
-- ============================================================================

private
  -- Head of `(showDecRat-dec-chars d ++ inner-rest) ++ outer-suffix` is
  -- non-hspace.  Two cases on the integer numerator: `-[1+ n ]` ⇒ `'-'`;
  -- `+ absNum` ⇒ `digitChar k` with `k < 10`.  Mirrors `decrat-suffix-
  -- stop` in the pre-3d.5.d EV_ proof and `showDecRat-chars-head-stop-
  -- isHSpace` in `Properties/Attributes/Type.agda`; kept local pending
  -- the cross-module consolidation flagged in `Format/ValueTable.agda`.
  -- Left-bracketed form matches the natural shape of `withWS (pair
  -- decRat …)` slots.
  decRat-head-non-hspace : ∀ (d : DecRat) (inner-rest outer-suffix : List Char)
    → SuffixStops isHSpace
        ((showDecRat-dec-chars d ++ₗ inner-rest) ++ₗ outer-suffix)
  decRat-head-non-hspace (mkDecRat ℤ-[1+ n ] a b cx) inner-rest outer-suffix
    with showDecRat-chars-head-dash n a b cx
  ... | _ , eq =
        subst (λ xs → SuffixStops isHSpace
                        ((xs ++ₗ inner-rest) ++ₗ outer-suffix))
              (sym eq) (∷-stop refl)
  decRat-head-non-hspace (mkDecRat (ℤ+ absNum) a b cx) inner-rest outer-suffix
    with showDecRat-chars-head-digit absNum a b cx
  ... | k , _ , _ , eq =
        subst (λ xs → SuffixStops isHSpace
                        ((xs ++ₗ inner-rest) ++ₗ outer-suffix))
              (sym eq) (∷-stop (digitChar-not-isHSpace k))

-- ============================================================================
-- WELL-FORMEDNESS — top-level builder
-- ============================================================================

-- Build `EmitsOK envVarFmt ev outer-suffix` from the single domain
-- precondition `EnvVarNameStop ev`.  Every other SuffixStops obligation
-- either reduces to `∷-stop refl` on a closed cons-list head (the fixed
-- chars `':'`, `'['`, `']'`, `'|'`, `';'`, `'\n'`, the synthesized
-- identifier names, the unit `"`, the env_id `'0'`, intra-segment ws),
-- or chains through one of the case-split helpers (`decRat-head-non-
-- hspace`, `emit-varTypeFmt-head-non-hspace`, `build-EmitsOK-varTypeFmt`).
-- The `newlineFmt`-inj₂ branch's altSum-disjointness witness closes by
-- `λ _ → refl`.
--
-- Tuple structure mirrors the L1–L25 layer chain in the file header
-- comment; comments name each layer's discharge.  Right-associative
-- `_,_` flattens the nested pairs.
-- L2 ws-witness factored out so its goal type stays compact.  The
-- `after-name-rest` parameter abstracts over the (long) format
-- continuation past the name; the call site passes `_` and Agda fills it
-- in from the surrounding EmitsOK goal.
private
  ws-slot1-witness : ∀ (ev : EnvironmentVar)
                       (after-name-rest outer-suffix : List Char)
    → EnvVarNameStop ev
    → SuffixStops isHSpace
        ((Identifier.name (EnvironmentVar.name ev) ++ₗ after-name-rest)
         ++ₗ outer-suffix)
  ws-slot1-witness ev after-name-rest outer-suffix
                   (c , cs , name-eq , c-non-hs) =
    subst (λ xs → SuffixStops isHSpace
                    ((xs ++ₗ after-name-rest) ++ₗ outer-suffix))
          (sym name-eq)
          (∷-stop c-non-hs)

build-emits-ok : ∀ (ev : EnvironmentVar) (outer-suffix : List Char)
  → EnvVarNameStop ev
  → EmitsOK envVarFmt ev outer-suffix
build-emits-ok ev outer-suffix nameStop =
    -- L1 (withPrefix "EV_"): inner literal vacuous.
    tt
    -- L2 (withWS) at ws slot 1: head of name is non-hspace via name-eq.
  , ws-slot1-witness ev _ outer-suffix nameStop
    -- L3 (pair ident L4): SuffixStops isIdentCont — head of L4-emit is `:`.
  , ∷-stop refl
    -- L4 (withWSOpt) at wsOpt slot 1 (post-name): head is `:`, non-hspace.
  , ∷-stop refl
    -- L5 (withPrefix ":"): inner literal vacuous.
  , tt
    -- L6 (withWS) at ws slot 2: head of L7-emit is varTypeFmt's emit head.
  , emit-varTypeFmt-head-non-hspace (EnvironmentVar.varType ev) _ outer-suffix
    -- L7 (pair varTypeFmt L8): per-VarType EmitsOK.
  , build-EmitsOK-varTypeFmt (EnvironmentVar.varType ev) _
    -- L8 (withWS) at ws slot 3: head of L9-emit is `[`.
  , ∷-stop refl
    -- L9 (withPrefix "["): inner literal vacuous.
  , tt
    -- L10 (pair decRat L11): SuffixStops isDigit — head of L11-emit is `|`.
  , ∷-stop refl
    -- L11 (withPrefix "|"): inner literal vacuous.
  , tt
    -- L12 (pair decRat L13): SuffixStops isDigit — head of L13-emit is `]`.
  , ∷-stop refl
    -- L13 (withPrefix "]"): inner literal vacuous.
  , tt
    -- L14 (withWS) at ws slot 4: head of L15-emit is `"` (unit), non-hspace.
  , ∷-stop refl
    -- L15 (pair (discardFmt [] stringLit) L16): SuffixStops (≈ᵇ '"') —
    -- head of L16-emit is ` ` (post-unit ws), non-`"`.
  , ∷-stop refl
    -- L16 (withWS) at ws slot 5: head of L17-emit is decRat ini head.
  , decRat-head-non-hspace (EnvironmentVar.initial ev) _ outer-suffix
    -- L17 (pair decRat L18): SuffixStops isDigit — head of L18-emit is ` `.
  , ∷-stop refl
    -- L18 (withWS) at ws slot 6: head of L19-emit is `0` (env_id), non-hspace.
  , ∷-stop refl
    -- L19 (pair (discardFmt 0 nat) L20): SuffixStops isDigit — head of
    -- L20-emit is ` ` (post-env_id ws), non-digit.
  , ∷-stop refl
    -- L20 (withWS) at ws slot 7: head of L21-emit is `D` (atype), non-hspace.
  , ∷-stop refl
    -- L21 (pair (discardFmt ident-DummyNode ident) L22): SuffixStops
    -- isIdentCont — head of L22-emit is ` ` (post-atype ws), non-isIdentCont.
  , ∷-stop refl
    -- L22 (withWS) at ws slot 8: head of L23-emit is `V` (anode), non-hspace.
  , ∷-stop refl
    -- L23 (pair (discardFmt ident-VectorXXX ident) L24): SuffixStops
    -- isIdentCont — head of L24-emit is `;` (next is wsOpt then ;), non-
    -- isIdentCont.
  , ∷-stop refl
    -- L24 (withWSOpt) at wsOpt slot 2 (post-anode): head is `;`, non-hspace.
  , ∷-stop refl
    -- L25 (withPrefix ";"): inner literal vacuous.
  , tt
    -- L26 (newlineFmt) inj₂ inner: literal "\n" vacuous + parse "\r\n"
    -- disjointness on '\n' ∷ outer-suffix.
  , tt
  , (λ _ → refl)

-- ============================================================================
-- TOP-LEVEL ROUNDTRIP — the universal-form theorem
-- ============================================================================

-- THE GATE: parseEnvVar's line-portion expressed via Format DSL.  Body is
-- one `roundtrip` call + the EmitsOK construction.  Universal in `ev`
-- and `outer-suffix`; the only domain precondition is `EnvVarNameStop
-- ev`, which Layer 4 will discharge universally from `validIdentifierᵇ`.
parseEnvVar-format-roundtrip :
    ∀ (pos : Position) (ev : EnvironmentVar) (outer-suffix : List Char)
  → EnvVarNameStop ev
  → parse envVarFmt pos
      (emit envVarFmt ev ++ₗ outer-suffix)
    ≡ just (mkResult ev
             (advancePositions pos (emit envVarFmt ev))
             outer-suffix)
parseEnvVar-format-roundtrip pos ev outer-suffix nameStop =
  roundtrip envVarFmt pos ev outer-suffix
    (build-emits-ok ev outer-suffix nameStop)
