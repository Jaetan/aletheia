{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4c task B — `many parseTopStmt` over a typed-shadow body
-- via `many-η-roundtrip-with-lift`.
--
-- Instantiation:
--   * I = TopStmtTyped, O = TopStmt
--   * P = parseTopStmt
--   * E = emitTopStmt-chars defs
--   * Stop = TopStmtTypedWF defs
--   * L = liftTopStmt defs
--
-- Backed by:
--   * `parseTopStmt-on-emitTopStmt-chars` (combined per-section
--     dispatcher) as `P-on-emit`.
--   * `emitTopStmt-chars-nonzero` / `emitTopStmt-chars-head-not-newline`
--     (uniform emitter facts; TAT case factors through the β prefix
--     witness in `Attribute/PrefixHead.agda`).
--
-- The result list is `map (liftTopStmt defs) ts`, which is exactly what
-- `partitionTopStmts` (task C) consumes.
module Aletheia.DBC.TextParser.Properties.Aggregator.ManyTopStmts where

open import Data.Char  using (Char)
open import Data.List  using (List; []; _∷_; foldr; map)
  renaming (_++_ to _++ₗ_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_)

open import Aletheia.Parser.Combinators using
  (Position; ParseResult; mkResult; advancePositions; many)

open import Aletheia.DBC.Types using
  (AttrDef)

open import Aletheia.DBC.TextParser.TopLevel using
  (TopStmt; parseTopStmt)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (SuffixStops)
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart)

open import Aletheia.DBC.TextParser.Properties.ManyRoundtrip using
  (many-η-roundtrip-with-lift)

open import Aletheia.DBC.TextParser.Properties.Aggregator.Foundations using
  ( TopStmtTyped
  ; emitTopStmt-chars
  ; liftTopStmt
  )
open import Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher using
  ( TopStmtTypedWF
  ; parseTopStmt-on-emitTopStmt-chars
  ; emitTopStmt-chars-nonzero
  ; emitTopStmt-chars-head-not-newline
  )

-- ============================================================================
-- LIST-LEVEL ROUNDTRIP — `many parseTopStmt` over a TopStmtTyped body
-- ============================================================================
--
-- `outer-suffix` carries the body terminator (e.g. the `[]` empty
-- suffix for a fully-consumed body, or whatever finalizeParse expects
-- after the last TopStmt).  The caller proves
-- `parseTopStmt pos' outer-suffix ≡ nothing` once and we lift it
-- through the whole body.

parseTopStmts-roundtrip :
    ∀ (defs : List AttrDef) (pos : Position) (ts : List TopStmtTyped)
      (outer-suffix : List Char)
  → All (TopStmtTypedWF defs) ts
  → SuffixStops isNewlineStart outer-suffix
  → (∀ (pos' : Position) → parseTopStmt pos' outer-suffix ≡ nothing)
  → many parseTopStmt pos
      (foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] ts ++ₗ outer-suffix)
    ≡ just (mkResult (map (liftTopStmt defs) ts)
             (advancePositions pos
               (foldr (λ t acc → emitTopStmt-chars defs t ++ₗ acc) [] ts))
             outer-suffix)
parseTopStmts-roundtrip defs pos ts outer-suffix ts-wfs os pf =
  many-η-roundtrip-with-lift
    parseTopStmt
    (emitTopStmt-chars defs)
    (TopStmtTypedWF defs)
    (liftTopStmt defs)
    (λ pos₁ t suffix wf nl-stop →
       parseTopStmt-on-emitTopStmt-chars defs pos₁ t suffix wf nl-stop)
    (emitTopStmt-chars-nonzero defs)
    (emitTopStmt-chars-head-not-newline defs)
    pos ts outer-suffix ts-wfs os pf
