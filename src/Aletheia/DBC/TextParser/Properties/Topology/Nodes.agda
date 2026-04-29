{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 3 3d.5.d — slim `parseBU-roundtrip` derived from the
-- universal Format DSL roundtrip.
--
-- Pre-3d.5.d (3b): hand-written 611-line bind-chain proof through 8 parser
-- primitives.
--
-- Post-3d.5.d: `parseBU = parse nodeListFmt >>= many parseNewline >>= pure`
-- (in `TextParser.Topology.SignalLine`), and the roundtrip reduces to:
--
--   1. A bridge `emit-nodeListFmt-eq-emitBU-chars-prefix` proving DSL emit
--      on `ns` (plus a trailing `'\n'`) equals existing `emitBU-chars ns`.
--   2. The universal `parseNodeList-format-roundtrip` (from `Format.Nodes`).
--   3. The trailing `many parseNewline` consuming the formatter's section-
--      blank `\n` (via `many-parseNewline-one-LF-stop` + `nl-stop`).
--   4. Position alignment via one `advancePositions-++` application + the
--      bridge (the 2-stage `pos-eq` pattern from 3d.8).
--
-- The `NodeNameStop` precondition migrates upstream to `Format.Nodes`;
-- this module re-exports it for source compatibility.
module Aletheia.DBC.TextParser.Properties.Topology.Nodes where

open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; map; foldr; length) renaming (_++_ to _++ₗ_)
open import Data.List.Properties using () renaming (++-assoc to ++ₗ-assoc)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just)
open import Data.Product using (_,_)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Aletheia.Parser.Combinators using
  (Parser; Position; ParseResult; mkResult;
   advancePosition; advancePositions;
   pure; _>>=_; many)
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.Types using (Node; mkNode)
open import Aletheia.DBC.TextParser.Lexer using (parseNewline)
open import Aletheia.DBC.TextParser.Topology.SignalLine using (parseBU)
open import Aletheia.DBC.TextFormatter.Topology using (emitBU-chars)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops; bind-just-step; advancePositions-++)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart; many-parseNewline-one-LF-stop)

open import Aletheia.DBC.TextParser.Format using
  (Format; emit; parse)
  renaming (many to manyF)
open import Aletheia.DBC.TextParser.Format.Nodes as FmtBU using
  (nodeListFmt; nodeEntry-format)

-- ============================================================================
-- RE-EXPORT — `NodeNameStop` migrated to `Format.Nodes`
-- ============================================================================

open import Aletheia.DBC.TextParser.Format.Nodes public
  using (NodeNameStop)

-- ============================================================================
-- BRIDGE: DSL emit ≡ existing emitBU-chars (with trailing `\n` displaced)
-- ============================================================================

-- Per-node: `emit nodeEntry-format n ≡ ' ' ∷ Identifier.name n` reduces
-- definitionally through `iso → pair → ws/ident`.  Closed by `refl`.
emit-nodeEntry-eq : ∀ (i : Identifier)
  → emit nodeEntry-format i ≡ ' ' ∷ Identifier.name i
emit-nodeEntry-eq _ = refl

-- Entries fold: `emit (manyF nodeEntry-format) (map Node.name ns) ++
-- terminator ≡ foldr (λ n acc → ' ' ∷ Identifier.name (Node.name n) ++ acc)
-- terminator ns`.  Closes by structural induction over `ns`; the cons case
-- unfolds `concatMap` then re-associates `++` to push `terminator` inside
-- the recursion.
emit-many-eq-foldr : ∀ (ns : List Node) (terminator : List Char)
  → emit (manyF nodeEntry-format) (map Node.name ns) ++ₗ terminator
    ≡ foldr (λ n acc → ' ' ∷ Identifier.name (Node.name n) ++ₗ acc) terminator ns
emit-many-eq-foldr [] terminator = refl
emit-many-eq-foldr (n ∷ rest) terminator =
  trans (++ₗ-assoc (emit nodeEntry-format (Node.name n))
                    (emit (manyF nodeEntry-format) (map Node.name rest))
                    terminator)
        (cong (emit nodeEntry-format (Node.name n) ++ₗ_)
              (emit-many-eq-foldr rest terminator))

-- Top-level bridge: full `emit nodeListFmt ns ++ '\n' ∷ [] ≡ emitBU-chars ns`.
-- LHS reduces (through nested isos / withPrefix / withWSOpt / pair) to:
--   toList "BU_:" ++ (emit (manyF nodeEntry-format) (map Node.name ns)
--                                                    ++ '\n' ∷ [])
-- + the displaced trailing `'\n' ∷ []` outside.  Two `++ₗ-assoc` steps
-- collapse this to `toList "BU_:" ++ (body ++ '\n' ∷ '\n' ∷ [])`, after
-- which `emit-many-eq-foldr ns ('\n' ∷ '\n' ∷ [])` bridges to
-- `toList "BU_:" ++ foldr (...) ('\n' ∷ '\n' ∷ []) ns ≡ emitBU-chars ns`
-- (the last step is `refl` since `toList "\n\n" ≡ '\n' ∷ '\n' ∷ []`
-- definitionally).
emit-nodeListFmt-eq-emitBU-chars-prefix : ∀ (ns : List Node)
  → emit nodeListFmt ns ++ₗ '\n' ∷ [] ≡ emitBU-chars ns
emit-nodeListFmt-eq-emitBU-chars-prefix ns =
  trans (++ₗ-assoc (toList "BU_:")
                    (emit (manyF nodeEntry-format) (map Node.name ns)
                     ++ₗ '\n' ∷ [])
                    ('\n' ∷ []))
   (cong (toList "BU_:" ++ₗ_)
     (trans (++ₗ-assoc (emit (manyF nodeEntry-format) (map Node.name ns))
                        ('\n' ∷ []) ('\n' ∷ []))
            (emit-many-eq-foldr ns ('\n' ∷ '\n' ∷ []))))

-- ============================================================================
-- SLIM `parseBU-roundtrip`
-- ============================================================================

-- Wrap-shaped: `parseBU = parse nodeListFmt >>= λ ns → many parseNewline
-- >>= λ _ → pure ns`.  Composition decomposes into:
--
--   1. Reshape input `emitBU-chars ns ++ suffix` to `emit nodeListFmt ns
--      ++ '\n' ∷ suffix` via the bridge + one `++ₗ-assoc`.
--   2. `parse nodeListFmt pos (emit nodeListFmt ns ++ '\n' ∷ suffix)` via
--      `parseNodeList-format-roundtrip`.
--   3. `many parseNewline pos' ('\n' ∷ suffix)` consumes one `'\n'` via
--      `many-parseNewline-one-LF-stop` + `nl-stop`.
--   4. `pure ns` returns the input value at the resulting position; convert
--      back to `advancePositions pos (emitBU-chars ns)` via
--      `advancePositions-++` + the bridge (2-stage pos-eq).
parseBU-roundtrip :
    ∀ (pos : Position) (ns : List Node) (suffix : List Char)
  → All NodeNameStop ns
  → SuffixStops isNewlineStart suffix
  → parseBU pos (emitBU-chars ns ++ₗ suffix)
    ≡ just (mkResult ns
             (advancePositions pos (emitBU-chars ns))
             suffix)
parseBU-roundtrip pos ns suffix node-stops nl-stop =
  trans (cong (λ inp → parseBU pos (inp ++ₗ suffix))
              (sym bridge))
    (trans step-shape
      (trans step-format
        (trans step-many-newline
          step-pure)))
  where
    bridge : emit nodeListFmt ns ++ₗ '\n' ∷ [] ≡ emitBU-chars ns
    bridge = emit-nodeListFmt-eq-emitBU-chars-prefix ns

    pos-line : Position
    pos-line = advancePositions pos (emit nodeListFmt ns)

    pos-after-nl : Position
    pos-after-nl = advancePosition pos-line '\n'

    cont-line : List Node → Parser (List Node)
    cont-line ns' = many parseNewline >>= λ _ → pure ns'

    cont-blanks : List Char → Parser (List Node)
    cont-blanks _ = pure ns

    -- Step 0: associativity reshape — push `'\n' ∷ []` from outside the
    -- bridge into the input prefix.  After this step the input is
    -- `emit nodeListFmt ns ++ '\n' ∷ suffix`.
    step-shape :
      parseBU pos ((emit nodeListFmt ns ++ₗ '\n' ∷ []) ++ₗ suffix)
      ≡ parseBU pos (emit nodeListFmt ns ++ₗ '\n' ∷ suffix)
    step-shape = cong (parseBU pos)
                      (++ₗ-assoc (emit nodeListFmt ns) ('\n' ∷ []) suffix)

    -- Step 1: parse nodeListFmt succeeds via the universal roundtrip.
    step-format :
      parseBU pos (emit nodeListFmt ns ++ₗ '\n' ∷ suffix)
      ≡ cont-line ns pos-line ('\n' ∷ suffix)
    step-format =
      bind-just-step (parse nodeListFmt)
                     cont-line
                     pos (emit nodeListFmt ns ++ₗ '\n' ∷ suffix)
                     ns pos-line ('\n' ∷ suffix)
                     (FmtBU.parseNodeList-format-roundtrip
                       pos ns ('\n' ∷ suffix) node-stops)

    -- Step 2: many parseNewline consumes exactly one `'\n'` from the
    -- residual `'\n' ∷ suffix` (suffix doesn't start with newline by
    -- precondition).
    step-many-newline :
      cont-line ns pos-line ('\n' ∷ suffix)
      ≡ cont-blanks ('\n' ∷ []) pos-after-nl suffix
    step-many-newline =
      bind-just-step (many parseNewline)
                     cont-blanks
                     pos-line ('\n' ∷ suffix)
                     ('\n' ∷ []) pos-after-nl suffix
                     (many-parseNewline-one-LF-stop
                       pos-line suffix (length suffix) nl-stop)

    -- Step 3: pure ns returns just (mkResult ns pos-after-nl suffix);
    -- collapse `pos-after-nl` to `advancePositions pos (emitBU-chars ns)`
    -- via the 2-stage pos-eq pattern from 3d.8.
    pos-eq : pos-after-nl ≡ advancePositions pos (emitBU-chars ns)
    pos-eq =
      trans
        (sym (advancePositions-++ pos (emit nodeListFmt ns) ('\n' ∷ [])))
        (cong (advancePositions pos) bridge)

    step-pure :
      cont-blanks ('\n' ∷ []) pos-after-nl suffix
      ≡ just (mkResult ns
               (advancePositions pos (emitBU-chars ns))
               suffix)
    step-pure = cong (λ p → just (mkResult ns p suffix)) pos-eq
