{-# OPTIONS --safe --without-K #-}

-- Proof-facing internals for the streaming protocol.
--
-- Purpose: Helper functions that are implementation details of handleDataFrame
-- but need to be accessible for proofs in FrameProcessor/Properties.agda.
-- Not part of the public streaming API.
--
-- Exports: Formula indexing (collectAtomsAcc, indexHelper, lookupAtom),
--   signal cache updates (updateSignals, updateCacheFromFrame),
--   PredTable construction (mkPredTable),
--   frame processing helpers (classifyStepResult, stepProperty, dispatchIterResult).
module Aletheia.Protocol.StreamState.Internals where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Function using (case_of_)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal)
open import Aletheia.LTL.Syntax using (LTL; Atomic; Not; And; Or; Next; Always; Eventually; Until; Release; MetricEventually; MetricAlways; MetricUntil; MetricRelease)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate; TruthVal; True; False; Unknown; SignalCache; updateCache; evalPredicateTV; extractTruthValue)
open import Aletheia.LTL.Incremental using (StepResult; Continue; Violated; Satisfied; Counterexample)
open import Aletheia.LTL.Coalgebra using (LTLProc; PredTable; stepL)
open import Aletheia.LTL.Simplify using (simplify)
open import Aletheia.Protocol.Message using (Response)
open import Aletheia.Protocol.StreamState.Types using (StreamState; mkStreamState; Streaming; PropertyState; mkPropertyState)
open import Aletheia.Trace.CANTrace using (TimedFrame)
open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.CAN.DBCHelpers using (findMessageById)
open import Aletheia.Protocol.Iteration using (StepOutcome; advance; halt)
open import Aletheia.Protocol.Response as PR using (mkCounterexampleData; PropertyResult)
open import Aletheia.Prelude using (listIndex)

-- ============================================================================
-- FORMULA INDEXING (LTL SignalPredicate → LTLProc + atom list)
-- ============================================================================

-- Collect all atomic predicates in left-to-right tree order (O(n) via accumulator).
collectAtomsAcc : LTL SignalPredicate → List SignalPredicate → List SignalPredicate
collectAtomsAcc (Atomic a)                 acc = a ∷ acc
collectAtomsAcc (Not φ)                    acc = collectAtomsAcc φ acc
collectAtomsAcc (And φ ψ)                  acc = collectAtomsAcc φ (collectAtomsAcc ψ acc)
collectAtomsAcc (Or φ ψ)                   acc = collectAtomsAcc φ (collectAtomsAcc ψ acc)
collectAtomsAcc (Next φ)                   acc = collectAtomsAcc φ acc
collectAtomsAcc (Always φ)                 acc = collectAtomsAcc φ acc
collectAtomsAcc (Eventually φ)             acc = collectAtomsAcc φ acc
collectAtomsAcc (Until φ ψ)                acc = collectAtomsAcc φ (collectAtomsAcc ψ acc)
collectAtomsAcc (Release φ ψ)              acc = collectAtomsAcc φ (collectAtomsAcc ψ acc)
collectAtomsAcc (MetricEventually _ _ φ)   acc = collectAtomsAcc φ acc
collectAtomsAcc (MetricAlways _ _ φ)       acc = collectAtomsAcc φ acc
collectAtomsAcc (MetricUntil _ _ φ ψ)      acc = collectAtomsAcc φ (collectAtomsAcc ψ acc)
collectAtomsAcc (MetricRelease _ _ φ ψ)    acc = collectAtomsAcc φ (collectAtomsAcc ψ acc)

-- The resulting list maps ℕ indices to predicates for PredTable construction.
collectAtoms : LTL SignalPredicate → List SignalPredicate
collectAtoms formula = collectAtomsAcc formula []

-- Replace each atom with its position index (counter-based, matches collectAtoms order)
indexHelper : LTL SignalPredicate → ℕ → LTL ℕ × ℕ
indexHelper (Atomic _) n            = (Atomic n , suc n)
indexHelper (Not φ) n               = let (φ' , n') = indexHelper φ n in (Not φ' , n')
indexHelper (And φ ψ) n             = let (φ' , n') = indexHelper φ n ; (ψ' , n'') = indexHelper ψ n' in (And φ' ψ' , n'')
indexHelper (Or φ ψ) n              = let (φ' , n') = indexHelper φ n ; (ψ' , n'') = indexHelper ψ n' in (Or φ' ψ' , n'')
indexHelper (Next φ) n              = let (φ' , n') = indexHelper φ n in (Next φ' , n')
indexHelper (Always φ) n            = let (φ' , n') = indexHelper φ n in (Always φ' , n')
indexHelper (Eventually φ) n        = let (φ' , n') = indexHelper φ n in (Eventually φ' , n')
indexHelper (Until φ ψ) n           = let (φ' , n') = indexHelper φ n ; (ψ' , n'') = indexHelper ψ n' in (Until φ' ψ' , n'')
indexHelper (Release φ ψ) n         = let (φ' , n') = indexHelper φ n ; (ψ' , n'') = indexHelper ψ n' in (Release φ' ψ' , n'')
indexHelper (MetricEventually w s φ) n    = let (φ' , n') = indexHelper φ n in (MetricEventually w s φ' , n')
indexHelper (MetricAlways w s φ) n        = let (φ' , n') = indexHelper φ n in (MetricAlways w s φ' , n')
indexHelper (MetricUntil w s φ ψ) n      = let (φ' , n') = indexHelper φ n ; (ψ' , n'') = indexHelper ψ n' in (MetricUntil w s φ' ψ' , n'')
indexHelper (MetricRelease w s φ ψ) n    = let (φ' , n') = indexHelper φ n ; (ψ' , n'') = indexHelper ψ n' in (MetricRelease w s φ' ψ' , n'')

indexFormula : LTL SignalPredicate → LTL ℕ
indexFormula φ = Data.Product.proj₁ (indexHelper φ 0)

-- Safe list indexing by ℕ (delegates to Prelude.listIndex with flipped args)
lookupAtom : List SignalPredicate → ℕ → Maybe SignalPredicate
lookupAtom xs n = listIndex n xs

-- Build PredTable from atom list + DBC + SignalCache
-- The table maps predicate indices to evaluation functions.
mkPredTable : DBC → SignalCache → List SignalPredicate → PredTable
mkPredTable dbc cache atoms n frame =
  case lookupAtom atoms n of λ where
    nothing     → Unknown
    (just pred) → evalPredicateTV dbc cache pred (TimedFrame.frame frame)

-- ============================================================================
-- SIGNAL CACHE UPDATES
-- ============================================================================

-- Update cache with all signals from a signal list.
updateSignals : ∀ {n} → DBC → CANFrame n → ℕ → List DBCSignal → SignalCache → SignalCache
updateSignals dbc frame ts [] c = c
updateSignals dbc frame ts (sig ∷ sigs) c =
  let sigName = DBCSignal.name sig
  in case extractTruthValue sigName dbc frame of λ where
    nothing  → updateSignals dbc frame ts sigs c
    (just v) → updateSignals dbc frame ts sigs (updateCache sigName v ts c)

-- Update cache with all signals extractable from a frame
updateCacheFromFrame : ∀ {n} → DBC → SignalCache → ℕ → CANFrame n → SignalCache
updateCacheFromFrame dbc cache ts frame =
  case findMessageById (CANFrame.id frame) dbc of λ where
    nothing    → cache
    (just msg) → updateSignals dbc frame ts (DBCMessage.signals msg) cache

-- ============================================================================
-- FRAME PROCESSING HELPERS
-- ============================================================================

-- Classify a single stepL result into a StepOutcome.
classifyStepResult : StepResult LTLProc → PropertyState → StepOutcome PropertyState (ℕ × Counterexample)
classifyStepResult (Continue _ newProc) prop =
  advance (mkPropertyState (PropertyState.index prop) (PropertyState.formula prop) (PropertyState.atoms prop) (simplify newProc))
classifyStepResult (Violated ce) prop = halt (PropertyState.index prop , ce)
classifyStepResult Satisfied prop = advance prop

-- Step one property: build PredTable, call stepL, classify result.
stepProperty : DBC → SignalCache → TimedFrame → PropertyState → StepOutcome PropertyState (ℕ × Counterexample)
stepProperty dbc cache tf prop =
  let table = mkPredTable dbc cache (PropertyState.atoms prop)
      result = stepL table (PropertyState.proc prop) tf
  in classifyStepResult result prop

-- Dispatch iteration result to StreamState × Response.
dispatchIterResult : DBC → List PropertyState × Maybe (ℕ × Counterexample) → TimedFrame → SignalCache → StreamState × Response
dispatchIterResult dbc (updatedProps , nothing) tf cache =
  (mkStreamState Streaming (just dbc) updatedProps (just tf) cache , Response.Ack)
dispatchIterResult dbc (allProps , just (idx , ce)) tf cache =
  let open Counterexample ce
      ceData = mkCounterexampleData (TimedFrame.timestamp violatingFrame) reason
      violation = PR.PropertyResult.Violation idx ceData
  in (mkStreamState Streaming (just dbc) allProps (just tf) cache , Response.PropertyResponse violation)
