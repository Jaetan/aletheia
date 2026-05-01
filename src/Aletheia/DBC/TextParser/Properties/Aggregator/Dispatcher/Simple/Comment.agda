{-# OPTIONS --safe --without-K #-}

-- B.3.d Layer 4c — TCM dispatcher under head-dispatched parseTopStmt.
--
-- `emitComment-chars c ++ outer` starts with 'C'∷'M' for every concrete
-- target.  Because `emitComment-chars` dispatches on `c.target` via a
-- `where`-helper, Agda only reduces the prefix once the target is
-- pattern-matched — so this module case-splits on `c.target` and emits
-- one bind-just-step per branch.  Each branch's parseTopStmt reduces to
-- the CM bucket: `parseComment >>= λ cm → pure (TSComment cm)`.
module Aletheia.DBC.TextParser.Properties.Aggregator.Dispatcher.Simple.Comment where

open import Data.Char  using (Char)
open import Data.List  using (List)
  renaming (_++_ to _++ₗ_)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality
  using (_≡_)

open import Aletheia.Parser.Combinators using
  (Position; ParseResult; mkResult; advancePositions;
   _>>=_; pure)

open import Aletheia.DBC.Types using
  (DBCComment; mkComment; CommentTarget;
   CTNetwork; CTNode; CTMessage; CTSignal; CTEnvVar)
open import Aletheia.DBC.TextParser.TopLevel using
  (TopStmt; TSComment; parseTopStmt)
open import Aletheia.DBC.TextParser.Comments using
  (parseComment)

open import Aletheia.DBC.TextFormatter.Comments using
  (emitComment-chars)

open import Aletheia.DBC.TextParser.Properties.Comments using
  (parseComment-roundtrip; CommentTargetStop)

open import Aletheia.DBC.TextParser.DecRatParse.Properties using
  (bind-just-step; SuffixStops)

open import Aletheia.DBC.TextParser.Properties.Preamble.Newline using
  (isNewlineStart)

parseTopStmt-on-emit-TCM-eq :
    ∀ (pos : Position) (c : DBCComment) (outer : List Char)
  → CommentTargetStop c
  → SuffixStops isNewlineStart outer
  → parseTopStmt pos (emitComment-chars c ++ₗ outer)
    ≡ just (mkResult (TSComment c)
                     (advancePositions pos (emitComment-chars c))
                     outer)
parseTopStmt-on-emit-TCM-eq pos c@(mkComment CTNetwork _) outer tgt-stop nl-stop =
  bind-just-step parseComment (λ cm → pure (TSComment cm))
    pos input c pos-c outer p-c-eq
  where
    input  = emitComment-chars c ++ₗ outer
    pos-c  = advancePositions pos (emitComment-chars c)
    p-c-eq = parseComment-roundtrip pos c outer tgt-stop nl-stop
parseTopStmt-on-emit-TCM-eq pos c@(mkComment (CTNode _) _) outer tgt-stop nl-stop =
  bind-just-step parseComment (λ cm → pure (TSComment cm))
    pos input c pos-c outer p-c-eq
  where
    input  = emitComment-chars c ++ₗ outer
    pos-c  = advancePositions pos (emitComment-chars c)
    p-c-eq = parseComment-roundtrip pos c outer tgt-stop nl-stop
parseTopStmt-on-emit-TCM-eq pos c@(mkComment (CTMessage _) _) outer tgt-stop nl-stop =
  bind-just-step parseComment (λ cm → pure (TSComment cm))
    pos input c pos-c outer p-c-eq
  where
    input  = emitComment-chars c ++ₗ outer
    pos-c  = advancePositions pos (emitComment-chars c)
    p-c-eq = parseComment-roundtrip pos c outer tgt-stop nl-stop
parseTopStmt-on-emit-TCM-eq pos c@(mkComment (CTSignal _ _) _) outer tgt-stop nl-stop =
  bind-just-step parseComment (λ cm → pure (TSComment cm))
    pos input c pos-c outer p-c-eq
  where
    input  = emitComment-chars c ++ₗ outer
    pos-c  = advancePositions pos (emitComment-chars c)
    p-c-eq = parseComment-roundtrip pos c outer tgt-stop nl-stop
parseTopStmt-on-emit-TCM-eq pos c@(mkComment (CTEnvVar _) _) outer tgt-stop nl-stop =
  bind-just-step parseComment (λ cm → pure (TSComment cm))
    pos input c pos-c outer p-c-eq
  where
    input  = emitComment-chars c ++ₗ outer
    pos-c  = advancePositions pos (emitComment-chars c)
    p-c-eq = parseComment-roundtrip pos c outer tgt-stop nl-stop
