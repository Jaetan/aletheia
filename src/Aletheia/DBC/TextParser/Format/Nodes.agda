{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.5.d — DSL-side `nodeListFmt` for the `BU_` (node-list)
-- DBC line.
--
-- The formatter emits `BU_:` + zero-or-more ` <name>` + `\n\n` (line
-- terminator + section blank line).  This Format produces the same line
-- minus the *second* `\n` — that one belongs to the wrapper's `many
-- parseNewline` so the section-blank semantics stay where they belong
-- (between sections, not inside the BU_ Format).  Same pattern as
-- `Format/ValueTable.agda`.
--
-- Whitespace fidelity (production-permissive, canonical-emit):
--   * `withWSOpt`      — between `BU_` and `:`, and between the last node
--                        and the line terminator (canonical empty emit;
--                        parser zero-or-more — both slots use
--                        `parseWSOpt` in the production parser).
--   * `withWS`         — between `:` and each node (canonical single space;
--                        parser one-or-more — `parseWS` per body iter).
--   * `newlineFmt`     — line terminator; canonical emit `'\n'`, parser
--                        accepts `'\n'` and `'\r\n'`.
--
-- The trailing `many parseNewline` consumption (the second `\n` plus any
-- additional blank lines after) lives in the
-- `Aletheia.DBC.TextParser.Topology.SignalLine.parseBU` wrapper, NOT in
-- this Format — same pattern as η's `parseSignalLine` / 3d.5.d's
-- `parseValueTable`.
module Aletheia.DBC.TextParser.Format.Nodes where

open import Data.Bool using (false)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; map) renaming (_++_ to _++ₗ_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (s≤s; z≤n)
open import Data.Product using (_×_; _,_; proj₂; Σ; Σ-syntax)
open import Data.String using (toList)
open import Data.Sum using (inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst)

open import Aletheia.Parser.Combinators
  using (Position; Parser; ParseResult; mkResult; advancePositions)
open import Aletheia.DBC.Identifier using (Identifier; isIdentCont)
open import Aletheia.DBC.Types using (Node; mkNode)
open import Aletheia.DBC.TextParser.Lexer using (isHSpace)
open import Aletheia.DBC.TextParser.DecRatParse.Properties
  using (SuffixStops; ∷-stop)
open import Aletheia.DBC.TextParser.Format
  using (Format; literal; ident; pair; iso; many;
         altSum; wsOpt; ws; withPrefix;
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

  -- Line terminator: accepts `"\r\n"` or `"\n"`, canonical emit `"\n"`.
  newlineFmt : Format ⊤
  newlineFmt = iso (λ _ → tt) (λ _ → inj₂ tt) (λ _ → refl)
                    (altSum (literal ('\r' ∷ '\n' ∷ []))
                            (literal ('\n' ∷ [])))

-- ============================================================================
-- η witness — `map mkNode (map Node.name ns) ≡ ns`
-- ============================================================================

-- Single-field record `Node` reduces `mkNode (Node.name n) ≡ n`
-- definitionally; the list induction lifts to the full equation.  The
-- pre-3d.5.d `Properties/Topology/Nodes.agda` had a private copy; this
-- copy is the canonical site post-migration.
private
  map-mkNode-Node-name : ∀ (ns : List Node)
    → map mkNode (map Node.name ns) ≡ ns
  map-mkNode-Node-name [] = refl
  map-mkNode-Node-name (n ∷ ns) = cong (n ∷_) (map-mkNode-Node-name ns)

-- ============================================================================
-- DSL DEFINITION
-- ============================================================================

-- A single ` <name>` entry — mandatory single space (`parseWS` /
-- canonical-emit `' ' ∷ []`) followed by the identifier.  Public so the
-- bridge proof in `Properties.Topology.Nodes` can reference the per-element
-- format.  Mirrors `ValueEntry-format`.
nodeEntry-format : Format Identifier
nodeEntry-format = withWS ident

-- `BU_:` + zero-or-more ` <name>` + line terminator.  Outer iso converts
-- from the underlying `(List Identifier × ⊤)` carrier to the user-facing
-- `List Node`.
nodeListFmt : Format (List Node)
nodeListFmt =
  iso fwd bwd map-mkNode-Node-name
    (withPrefix (toList "BU_") (
     withWSOpt (
      withPrefix (':' ∷ []) (
       pair (many nodeEntry-format) (
        withWSOpt newlineFmt)))))
  where
    fwd : List Identifier × ⊤ → List Node
    fwd (names , _) = map mkNode names

    bwd : List Node → List Identifier × ⊤
    bwd ns = map Node.name ns , tt

-- ============================================================================
-- PER-NODE PRECONDITION
-- ============================================================================

-- Each node's name decomposes as `c ∷ cs` with `isHSpace c ≡ false`,
-- discharging the `withWS ident` slot's `SuffixStops isHSpace
-- (Identifier.name (Node.name n) ++ rest)` obligation via `∷-stop
-- c-non-hspace`.  Mirrors `ValueTableNameStop`; Layer 4 will discharge
-- this universally from `validIdentifierᵇ` via the
-- `isIdentStart→¬isHSpace` bridge (see
-- `project_b3d_layer4_owed_lemmas.md`).
NodeNameStop : Node → Set
NodeNameStop n =
  Σ[ c ∈ Char ] Σ[ cs ∈ List Char ]
    (Identifier.name (Node.name n) ≡ c ∷ cs) × (isHSpace c ≡ false)

-- ============================================================================
-- TERMINATION CERTIFICATE — `parse nodeEntry-format` rejects `'\n' ∷ …`
-- ============================================================================

-- `parse nodeEntry-format pos ('\n' ∷ rest)` fires `parseWS` first, and
-- `parseWS = some (satisfy isHSpace)` rejects `'\n'` (not hspace), so the
-- bind chain returns `nothing`.  `refl` because every step reduces
-- definitionally on the closed leading char.  Provides `ParseFailsAt
-- nodeEntry-format ('\n' ∷ outer)` for the empty-tail step of `EmitsOKMany`.
parse-nodeEntry-fails-on-LF : ∀ pos rest
  → parse nodeEntry-format pos ('\n' ∷ rest) ≡ nothing
parse-nodeEntry-fails-on-LF pos rest = refl

-- ============================================================================
-- WELL-FORMEDNESS — per-node EmitsOK
-- ============================================================================

-- Build `EmitsOK nodeEntry-format (Node.name n) outer-rest` from a single
-- domain precondition (`NodeNameStop n`) plus the head-of-`outer-rest`
-- isIdentCont witness.  Reduces structurally through `iso` and `pair` to
-- a SuffixStops × SuffixStops pair.
build-EmitsOK-node : ∀ (n : Node) (outer-rest : List Char)
  → NodeNameStop n
  → SuffixStops isIdentCont outer-rest
  → EmitsOK nodeEntry-format (Node.name n) outer-rest
build-EmitsOK-node n outer-rest (c , cs , name-eq , c-non-hs) outer-stop =
  (subst (λ xs → SuffixStops isHSpace (xs ++ₗ outer-rest))
         (sym name-eq)
         (∷-stop c-non-hs))
  , outer-stop

-- ============================================================================
-- WELL-FORMEDNESS — node list (EmitsOKMany)
-- ============================================================================

-- `EmitsOKMany nodeEntry-format (map Node.name ns) ('\n' ∷ outer-suffix)`.
-- Empty:  []-fails via `parse-nodeEntry-fails-on-LF`.
-- Cons (last):  per-node EmitsOK against trailing `'\n' ∷ …`; recursive [] step.
-- Cons (non-last):  per-node EmitsOK against next entry's leading `' '`;
--                   recursive cons step.
build-EmitsOKMany : ∀ (ns : List Node) (outer-suffix : List Char)
  → All NodeNameStop ns
  → EmitsOKMany nodeEntry-format (map Node.name ns)
      ('\n' ∷ outer-suffix)
build-EmitsOKMany [] outer-suffix _ =
  []-fails (λ pos →
    parse-nodeEntry-fails-on-LF pos outer-suffix)
build-EmitsOKMany (n ∷ []) outer-suffix (n-stop ∷ _) =
  ∷-cons
    (build-EmitsOK-node n ('\n' ∷ outer-suffix) n-stop (∷-stop refl))
    (s≤s z≤n)
    (build-EmitsOKMany [] outer-suffix [])
build-EmitsOKMany (n ∷ (n' ∷ rest')) outer-suffix (n-stop ∷ rest-stops) =
  ∷-cons
    (build-EmitsOK-node n
       (emit (many nodeEntry-format) (map Node.name (n' ∷ rest'))
        ++ₗ '\n' ∷ outer-suffix)
       n-stop
       (∷-stop refl))
    (s≤s z≤n)
    (build-EmitsOKMany (n' ∷ rest') outer-suffix rest-stops)

-- ============================================================================
-- WELL-FORMEDNESS — top-level builder
-- ============================================================================

-- Build `EmitsOK nodeListFmt ns outer-suffix` from `All NodeNameStop ns`.
-- Reduces structurally through `iso → withPrefix → withWSOpt → withPrefix
-- → pair → many → withWSOpt → newlineFmt`.  Every SuffixStops obligation
-- either chains to a per-node `NodeNameStop` witness (inside the many-list
-- builder) or reduces to `∷-stop refl` on a closed-head fixed char (`':'`,
-- `'\n'`).  The altSum branch of `newlineFmt` discharges its disjointness
-- via `λ pos → refl` (`parse "\r\n"` rejects `'\n' ∷ …` on the first char).
build-emits-ok : ∀ (ns : List Node) (outer-suffix : List Char)
  → All NodeNameStop ns
  → EmitsOK nodeListFmt ns outer-suffix
build-emits-ok ns outer-suffix node-stops =
  -- "BU_" literal: vacuous.
  tt ,
  -- (withWSOpt ...) at slot 1: SuffixStops isHSpace (':' ∷ ...).
  ∷-stop refl ,
  -- (withPrefix ":" ...): inner literal vacuous.
  tt ,
  -- (many (withWS ident)) (map Node.name ns) against ('\n' ∷ outer-suffix).
  build-EmitsOKMany ns outer-suffix node-stops ,
  -- (withWSOpt newlineFmt) at slot 2: SuffixStops isHSpace ('\n' ∷ outer-suffix).
  ∷-stop refl ,
  -- (newlineFmt) inj₂ inner: literal "\n" vacuous + parse "\r\n"
  -- disjointness on ('\n' ∷ outer-suffix).
  tt ,
  λ _ → refl

-- ============================================================================
-- TOP-LEVEL ROUNDTRIP — the universal-form theorem
-- ============================================================================

-- THE GATE: parseBU's line-portion expressed via Format DSL.  Body is one
-- `roundtrip` call + the EmitsOK construction.  Universal in `ns` and
-- `outer-suffix`; the only domain precondition is `All NodeNameStop ns`,
-- which Layer 4 will discharge universally from `validIdentifierᵇ`.
parseNodeList-format-roundtrip :
    ∀ (pos : Position) (ns : List Node) (outer-suffix : List Char)
  → All NodeNameStop ns
  → parse nodeListFmt pos
      (emit nodeListFmt ns ++ₗ outer-suffix)
    ≡ just (mkResult ns
             (advancePositions pos (emit nodeListFmt ns))
             outer-suffix)
parseNodeList-format-roundtrip pos ns outer-suffix node-stops =
  roundtrip nodeListFmt pos ns outer-suffix
    (build-emits-ok ns outer-suffix node-stops)
