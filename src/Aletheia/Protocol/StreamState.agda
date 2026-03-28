{-# OPTIONS --safe --without-K #-}

-- Streaming protocol state machine, types, and LTL frame processing.
--
-- Purpose: Define state types and implement LTL property checking pipeline.
-- States: WaitingForDBC → ReadyToStream → Streaming.
-- Exports: State types (StreamState, PropertyState), formula indexing,
--   signal cache, LTL frame processing (handleDataFrame).
-- Role: Core state machine types and LTL evaluation used by Handlers and Main.
--
-- Command handlers live in Protocol/Handlers.agda (concern separation).
-- State machine enforces: DBC must be loaded before properties, properties before streaming.
-- LTL checking: Incremental stateful evaluation (O(1) memory) with immediate violation reporting.
module Aletheia.Protocol.StreamState where

open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁)
open import Function using (case_of_)
open import Aletheia.DBC.Types using (DBC; DBCMessage; DBCSignal)
open import Aletheia.LTL.Syntax using (LTL; Atomic; Not; And; Or; Next; Always; Eventually; Until; Release; MetricEventually; MetricAlways; MetricUntil; MetricRelease)
open import Aletheia.LTL.SignalPredicate using (SignalPredicate; TruthVal; True; False; Unknown; SignalCache; emptyCache; updateCache; evalPredicateTV; extractTruthValue)
open import Aletheia.LTL.Incremental using (StepResult; Continue; Violated; Satisfied; Counterexample)
open import Aletheia.LTL.Coalgebra using (LTLProc; PredTable; stepL; initProc; simplify)
open import Aletheia.Protocol.Message using (Response)
open import Aletheia.Trace.CANTrace using (TimedFrame)
open import Aletheia.CAN.Frame using (CANFrame)
open import Aletheia.CAN.DBCHelpers using (findMessageById)
open import Aletheia.Protocol.Iteration using (StepOutcome; advance; halt; iterate)
open import Aletheia.Protocol.Response as PR using (mkCounterexampleData; PropertyResult)

-- ============================================================================
-- STREAM STATE
-- ============================================================================

-- State machine for streaming protocol
data StreamPhase : Set where
  WaitingForDBC : StreamPhase      -- Initial state, waiting for ParseDBC
  ReadyToStream : StreamPhase      -- DBC parsed, waiting for SetProperties or StartStream
  Streaming : StreamPhase          -- Active streaming mode

-- Property with evaluation state for incremental checking
record PropertyState : Set where
  constructor mkPropertyState
  field
    index : ℕ
    formula : LTL SignalPredicate    -- Original formula (for display/JSON)
    atoms : List SignalPredicate     -- Collected atomic predicates (for PredTable)
    proc : LTLProc                   -- ℕ-indexed formula state (for stepL)

-- Complete stream state
record StreamState : Set where
  constructor mkStreamState
  field
    phase : StreamPhase
    dbc : Maybe DBC
    properties : List PropertyState    -- Properties with incremental eval state
    prevFrame : Maybe TimedFrame       -- Previous frame for ChangedBy predicate
    signalCache : SignalCache          -- Last-known signal values for three-valued semantics

-- Initial empty state
initialState : StreamState
initialState = mkStreamState WaitingForDBC nothing [] nothing emptyCache

-- ============================================================================
-- HELPER FUNCTIONS
-- ============================================================================

-- ============================================================================
-- FORMULA INDEXING (LTL SignalPredicate → LTLProc + atom list)
-- ============================================================================

-- Collect all atomic predicates in left-to-right tree order (O(n) via accumulator).
-- Factored to module level for proof access.
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
indexFormula φ = proj₁ (indexHelper φ 0)

-- Safe list indexing by ℕ
lookupAtom : List SignalPredicate → ℕ → Maybe SignalPredicate
lookupAtom []       _       = nothing
lookupAtom (x ∷ _)  zero    = just x
lookupAtom (_ ∷ xs) (suc n) = lookupAtom xs n

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
-- Factored to module level for proof access.
updateSignals : ∀ {n} → DBC → CANFrame n → ℕ → List DBCSignal → SignalCache → SignalCache
updateSignals dbc frame ts [] c = c
updateSignals dbc frame ts (sig ∷ sigs) c =
  let sigName = DBCSignal.name sig
  in case extractTruthValue sigName dbc frame of λ where
    nothing  → updateSignals dbc frame ts sigs c
    (just v) → updateSignals dbc frame ts sigs (updateCache sigName v ts c)

-- Update cache with all signals extractable from a frame
-- Iterates through all messages in DBC, finds matching message by ID,
-- then extracts and caches all its signals
updateCacheFromFrame : ∀ {n} → DBC → SignalCache → ℕ → CANFrame n → SignalCache
updateCacheFromFrame dbc cache ts frame =
  case findMessageById (CANFrame.id frame) dbc of λ where
    nothing    → cache
    (just msg) → updateSignals dbc frame ts (DBCMessage.signals msg) cache

-- ============================================================================
-- FRAME PROCESSING HELPERS (factored to module level for proof access)
-- ============================================================================

-- Classify a single stepL result into a StepOutcome.
-- Continue/Satisfied → advance (property continues checking)
-- Violated → halt (property failed, halt iteration)
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
-- nothing → Ack (all properties continued/satisfied)
-- just (idx, ce) → PropertyResponse Violation
dispatchIterResult : DBC → List PropertyState × Maybe (ℕ × Counterexample) → TimedFrame → SignalCache → StreamState × Response
dispatchIterResult dbc (updatedProps , nothing) tf cache =
  (mkStreamState Streaming (just dbc) updatedProps (just tf) cache , Response.Ack)
dispatchIterResult dbc (allProps , just (idx , ce)) tf cache =
  let open Counterexample ce
      ceData = mkCounterexampleData (TimedFrame.timestamp violatingFrame) reason
      violation = PR.PropertyResult.Violation idx ceData
  in (mkStreamState Streaming (just dbc) allProps (just tf) cache , Response.PropertyResponse violation)

-- ============================================================================
-- FRAME PROCESSING (LTL Checking)
-- ============================================================================

-- Process incoming CAN frame with incremental LTL property checking.
--
-- In Streaming phase: updates signal cache, iterates stepProperty over all
-- properties (calling stepL for each), dispatches result to Ack or Violation.
--
-- O(1) Memory: Properties maintain fixed-size LTLProc state (no trace accumulation).
-- Violation Reporting: First violation halts iteration with counterexample evidence.
handleDataFrame : StreamState → TimedFrame → StreamState × Response
handleDataFrame state tf with StreamState.phase state
... | WaitingForDBC = (state , Response.Error "DataFrame: DBC not loaded")
... | ReadyToStream = (state , Response.Error "DataFrame: stream not started")
... | Streaming with StreamState.dbc state
...   | nothing = (state , Response.Error "DataFrame: DBC not loaded")
...   | just dbc =
  let cache = StreamState.signalCache state
      updatedCache = updateCacheFromFrame dbc cache (TimedFrame.timestamp tf) (TimedFrame.frame tf)
  in dispatchIterResult dbc (iterate (stepProperty dbc cache tf) (StreamState.properties state)) tf updatedCache

