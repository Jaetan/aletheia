-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Every property index a reply carries is below the count of properties the
-- session holds, and that count is the length of the list the last
-- accepted set_properties was handed.
--
-- Purpose: A binding reads a result's or a warning's `property_index`
--   straight into the list of properties it sent.  The theorems here are
--   what make that sound: a set_properties that succeeds leaves exactly as
--   many properties as it was handed and one refused leaves the session as
--   it was; a DBC load leaves none or leaves the session as it was; every
--   other command keeps the count; and every frame, trace event and end of
--   stream replies with indices below the count of the session it ran in.
-- Key results: handleSetProperties-settles, handleDataFrame-keeps,
--   handleTraceEvent-keeps, handleEndStream-keeps, handleStartStream-keeps,
--   handleParseDBC-loads, handleParseDBCText-loads, handleValidateDBC-keeps,
--   handleFormatDBCText-keeps.
module Aletheia.Protocol.FrameProcessor.Properties.PropertyIndex where

open import Aletheia.CAN.DBCHelpers using (dbcHasSignal)
open import Aletheia.DBC.Bounds using (checkBounds; scanText)
open import Aletheia.DBC.TextParser using (parseTextChars)
open import Aletheia.Parser.Position using (initialPosition)
open import Aletheia.DBC.JSONParser using (parseDBCWithErrors)
open import Aletheia.DBC.Validated using (validate)
open import Aletheia.DBC.Validity using (ValidDBC)
open import Aletheia.Error using (PropertyParseFailed)
open import Aletheia.LTL.Coalgebra using (finalizeL)
open import Aletheia.LTL.Incremental using (FinalVerdict; Holds; Fails; Unsure; Counterexample)
open import Aletheia.LTL.SignalPredicate using (SignalCache; SignalPredicate; signalOf; lookupCache)
open import Aletheia.LTL.SignalPredicate.Cache using (withForcedCache; withForcedCache-id)
open import Aletheia.LTL.SignalPredicate.Evaluation using (withForcedTable-id)
open import Aletheia.Protocol.Handlers using
  ( handleSetProperties; setPropertiesWithin; parseAllProperties; withIndices; readProperty
  ; handleStartStream; handleEndStream; handleParseDBC; handleValidateDBC
  ; finalizeProperties; verdictToResult
  ; collectUncachedWarnings; uncachedAtomWarnings
  )
open import Aletheia.Protocol.Handlers.FormatDBCText using (handleFormatDBCText)
open import Aletheia.Protocol.Handlers.LoadDBC using (loadValidatedDBC)
open import Aletheia.Protocol.Handlers.ParseDBCText using
  (handleParseDBCText; handleParseDBCTextResult; afterScan)
open import Aletheia.Protocol.Iteration using (iterate)
open import Aletheia.Protocol.Message using (Response)
open import Aletheia.Protocol.Response using (PropertyResult; Warning)
open import Aletheia.Protocol.StreamState using
  ( StreamState; WaitingForDBC; ReadyToStream; Streaming; PropertyState
  ; handleDataFrame; handleTraceEvent; checkMonotonic )
open import Aletheia.Protocol.StreamState.Internals using
  (extractTable; cacheFromTable; readableSignals; stepProperty; dispatchIterResult)
open import Aletheia.Trace.CANTrace using (TimedFrame; Data; Remote; timestamp)

open import Data.Bool using (true; false)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _<_; _<ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (toList)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Aletheia.Limits using (max-properties-per-stream)

-- ============================================================================
-- THE COUNT AND THE INDICES
-- ============================================================================

-- The number of properties a session holds.
propertyCount : StreamState → ℕ
propertyCount WaitingForDBC             = 0
propertyCount (ReadyToStream n _ _ _)   = n
propertyCount (Streaming n _ _ _ _)     = n

-- The property a result names.
resultIndex : PropertyResult → ℕ
resultIndex (PropertyResult.Violation i _)  = i
resultIndex (PropertyResult.Satisfaction i) = i
resultIndex (PropertyResult.Unresolved i _) = i

-- Every property index a reply carries is below `n`; a reply carrying none
-- holds trivially.
IndicesBelow : ℕ → Response → Set
IndicesBelow n (Response.PropertyResponse rs _) = All (λ r → resultIndex r < n) rs
IndicesBelow n (Response.Complete rs ws) =
  All (λ r → resultIndex r < n) rs × All (λ w → Warning.propertyIndex w < n) ws
IndicesBelow _ _ = ⊤

-- A step from `st` that replies with indices below `st`'s count and keeps it.
Keeps : StreamState → StreamState × Response → Set
Keeps st p = IndicesBelow (propertyCount st) (proj₂ p) × propertyCount (proj₁ p) ≡ propertyCount st

-- A set_properties step: on success the count is `k`, on any refusal the
-- session is as it was.
Settled : ℕ → StreamState → StreamState × Response → Set
Settled k st (st′ , Response.Success _) = propertyCount st′ ≡ k
Settled _ st (st′ , _)                  = st′ ≡ st

-- A DBC load: the session holds no property, or is as it was.
Loads : StreamState → StreamState × Response → Set
Loads st p = propertyCount (proj₁ p) ≡ 0 ⊎ proj₁ p ≡ st

-- ============================================================================
-- FRAMES, TRACE EVENTS, THE START AND THE END OF A STREAM
-- ============================================================================

private
  satisfactions-below : ∀ {n} (is : List (Fin n))
    → All (λ r → resultIndex r < n) (Data.List.map (λ i → PropertyResult.Satisfaction (toℕ i)) is)
  satisfactions-below []       = []
  satisfactions-below (i ∷ is) = toℕ<n i ∷ satisfactions-below is

-- The dispatcher's reply names only the `Fin n` indices it was handed.
dispatchIterResult-keeps : ∀ {n} vdbc (ir : List (PropertyState n) × Maybe (Fin n × Counterexample) × List (Fin n)) tf cache
  → IndicesBelow n (proj₂ (dispatchIterResult vdbc ir tf cache))
    × propertyCount (proj₁ (dispatchIterResult vdbc ir tf cache)) ≡ n
dispatchIterResult-keeps _ (_ , nothing , [])               _ _ = tt , refl
dispatchIterResult-keeps _ (_ , nothing , c ∷ cs)           _ _ = satisfactions-below (c ∷ cs) , refl
dispatchIterResult-keeps _ (_ , just (idx , _) , completions) _ _ =
  ++⁺ (satisfactions-below completions) (toℕ<n idx ∷ []) , refl

-- THEOREM: a data frame's reply names properties below the session's count,
-- and the count is kept.
handleDataFrame-keeps : ∀ st tf → Keeps st (handleDataFrame st tf)
handleDataFrame-keeps WaitingForDBC           _ = tt , refl
handleDataFrame-keeps (ReadyToStream _ _ _ _) _ = tt , refl
handleDataFrame-keeps (Streaming n vdbc props prev cache) tf with checkMonotonic prev tf
... | just _  = tt , refl
... | nothing =
  subst (Keeps (Streaming n vdbc props prev cache))
    (sym (trans (withForcedTable-id table (withForcedCache c′ k)) (withForcedCache-id c′ k)))
    (dispatchIterResult-keeps vdbc ir tf c′)
  where
    table = extractTable (ValidDBC.dbc vdbc) (TimedFrame.frame tf) (readableSignals props)
    c′    = cacheFromTable (timestamp tf) table cache
    ir    = iterate (stepProperty (ValidDBC.dbc vdbc) table cache tf) props
    k     = dispatchIterResult vdbc ir tf

-- THEOREM: a trace event's reply names properties below the session's
-- count, and the count is kept.
handleTraceEvent-keeps : ∀ st ev → Keeps st (handleTraceEvent st ev)
handleTraceEvent-keeps st (Data tf)       = handleDataFrame-keeps st tf
handleTraceEvent-keeps st (Aletheia.Trace.CANTrace.Error _) = tt , refl
handleTraceEvent-keeps st (Remote _ _)    = tt , refl

-- THEOREM: starting a stream keeps the count.
handleStartStream-keeps : ∀ st → Keeps st (handleStartStream st)
handleStartStream-keeps WaitingForDBC             = tt , refl
handleStartStream-keeps (ReadyToStream _ _ _ _)   = tt , refl
handleStartStream-keeps (Streaming _ _ _ _ _)     = tt , refl

private
  verdict-below : ∀ {n} (i : Fin n) (v : FinalVerdict) → resultIndex (verdictToResult i v) < n
  verdict-below i Holds      = toℕ<n i
  verdict-below i (Fails _)  = toℕ<n i
  verdict-below i (Unsure _) = toℕ<n i

  finalize-below : ∀ {n} (props : List (PropertyState n))
    → All (λ r → resultIndex r < n) (finalizeProperties props)
  finalize-below []         = []
  finalize-below (ps ∷ pss) =
    verdict-below (PropertyState.index ps) (finalizeL (PropertyState.proc ps)) ∷ finalize-below pss

  uncached-below : ∀ {n} k → k < n → ∀ cache (sps : List SignalPredicate)
    → All (λ w → Warning.propertyIndex w < n) (uncachedAtomWarnings k cache sps)
  uncached-below k k<n cache []         = []
  uncached-below k k<n cache (sp ∷ sps) with lookupCache (signalOf sp) cache
  ... | just _  = uncached-below k k<n cache sps
  ... | nothing = k<n ∷ uncached-below k k<n cache sps

  warnings-below : ∀ {n} (cache : SignalCache) (props : List (PropertyState n))
    → All (λ w → Warning.propertyIndex w < n) (collectUncachedWarnings cache props)
  warnings-below cache []         = []
  warnings-below cache (ps ∷ pss) =
    ++⁺ (uncached-below (toℕ (PropertyState.index ps)) (toℕ<n (PropertyState.index ps)) cache (PropertyState.atoms ps))
        (warnings-below cache pss)

-- THEOREM: the end of a stream replies with results and warnings naming
-- properties below the session's count, and keeps the count.
handleEndStream-keeps : ∀ st → Keeps st (handleEndStream st)
handleEndStream-keeps WaitingForDBC                     = tt , refl
handleEndStream-keeps (ReadyToStream _ _ _ _)           = tt , refl
handleEndStream-keeps (Streaming n vdbc props _ cache)  =
  (finalize-below props , warnings-below cache props) , refl

-- ============================================================================
-- SET_PROPERTIES
-- ============================================================================

-- The parse of a property list ends with the count it was given, or is
-- refused and leaves the session as it was.
parseAllProperties-settles : ∀ n st vdbc xs acc → Settled n st (parseAllProperties n st vdbc xs acc)
parseAllProperties-settles n st vdbc []                  acc = refl
parseAllProperties-settles n st vdbc ((idx , json) ∷ rest) acc
  with readProperty (dbcHasSignal (ValidDBC.dbc vdbc)) (PropertyParseFailed (toℕ idx)) json
... | inj₁ _ = refl
... | inj₂ _ = parseAllProperties-settles n st vdbc rest _

setPropertiesWithin-settles : ∀ js st vdbc b (eq : (length js <ᵇ suc max-properties-per-stream) ≡ b)
  → Settled (length js) st (setPropertiesWithin js st vdbc b eq)
setPropertiesWithin-settles js st vdbc false _ = refl
setPropertiesWithin-settles js st vdbc true  _ = parseAllProperties-settles (length js) st vdbc (withIndices js) []

-- THEOREM: a set_properties that succeeds leaves exactly as many properties
-- as the list it was handed; one refused leaves the session as it was.
handleSetProperties-settles : ∀ js st → Settled (length js) st (handleSetProperties js st)
handleSetProperties-settles js WaitingForDBC = refl
handleSetProperties-settles js st@(ReadyToStream _ vdbc _ _) =
  setPropertiesWithin-settles js st vdbc _ refl
handleSetProperties-settles js (Streaming _ _ _ _ _) = refl

-- ============================================================================
-- DBC LOADS AND THE COMMANDS THAT KEEP THE SESSION
-- ============================================================================

-- THEOREM: a DBC load leaves no property, or leaves the session as it was.
loadValidatedDBC-loads : ∀ ctx dbc st → Loads st (loadValidatedDBC ctx dbc st)
loadValidatedDBC-loads ctx dbc st with checkBounds dbc
... | inj₁ _ = inj₂ refl
... | inj₂ b with validate b
...   | inj₁ _ = inj₂ refl
...   | inj₂ _ = inj₁ refl

handleParseDBC-loads : ∀ j st → Loads st (handleParseDBC j st)
handleParseDBC-loads j st with parseDBCWithErrors j
... | inj₁ _   = inj₂ refl
... | inj₂ dbc = loadValidatedDBC-loads "ParseDBC" dbc st

handleParseDBCTextResult-loads : ∀ r st → Loads st (handleParseDBCTextResult r st)
handleParseDBCTextResult-loads (inj₁ _)   st = inj₂ refl
handleParseDBCTextResult-loads (inj₂ dbc) st = loadValidatedDBC-loads "ParseDBCText" dbc st

afterScan-loads : ∀ m cs st → Loads st (afterScan m cs st)
afterScan-loads (just _) _  st = inj₂ refl
afterScan-loads nothing  cs st = handleParseDBCTextResult-loads (parseTextChars cs) st

handleParseDBCText-loads : ∀ text st → Loads st (handleParseDBCText text st)
handleParseDBCText-loads text st =
  afterScan-loads (scanText initialPosition (toList text)) (toList text) st

-- THEOREM: validating a DBC and formatting one as text leave the session as
-- it was.
handleValidateDBC-keeps : ∀ j st → proj₁ (handleValidateDBC j st) ≡ st
handleValidateDBC-keeps j st with parseDBCWithErrors j
... | inj₁ _   = refl
... | inj₂ dbc with checkBounds dbc
...   | inj₁ _ = refl
...   | inj₂ _ = refl

handleFormatDBCText-keeps : ∀ j st → proj₁ (handleFormatDBCText j st) ≡ st
handleFormatDBCText-keeps _ _ = refl
