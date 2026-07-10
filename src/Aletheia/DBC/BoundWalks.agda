-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Shared handler-boundary bound walks over `DBC` and its substructures.
--
-- Purpose: extract the cardinality (`vds*` family + `totalValueDescriptions`)
-- and string-length (`firstOverBound*` family) walks that were duplicated
-- between `Aletheia.Protocol.Handlers` (JSON command path) and
-- `Aletheia.Protocol.Handlers.ParseDBCText` (verified text-parser path).
--
-- The original duplication was cycle-avoidance: `Handlers` imports
-- `Handlers.ParseDBCText`, so `ParseDBCText` could not import from
-- `Handlers` without closing the cycle.  Pulling the shared walks into
-- this leaf module (it imports only `DBC.Types` + `Limits`) gives both
-- consumers a common source.
--
-- Functions exported here are the *underlying* walks that return
-- `Maybe (ℕ × ℕ)` carrying `(observed , limit)` only.  Each consumer
-- attaches its own (or no) `String` field-context tag in its top-level
-- aggregator (`firstStringOverBound` / `firstDBCOverBound`) — the
-- naming differs by site (`Handlers` carries field names for richer
-- JSON error messages, `ParseDBCText` does not) which keeps that
-- choice local to the call site rather than baked into the helpers.
module Aletheia.DBC.BoundWalks where

open import Data.Bool using (true; false)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_; _<ᵇ_)
open import Data.Product using (_×_; _,_)
open import Aletheia.DBC.Types using
  ( DBC; DBCMessage; DBCSignal; ValueTable; RawValueDesc; DBCComment
  ; DBCAttribute; DBCAttrDef; DBCAttrDefault; DBCAttrAssign
  ; AttrDef; AttrDefault; AttrAssign; AttrType; ATEnum; AttrValue; AVString
  )
open import Aletheia.Limits using (max-string-length-bytes)

-- ============================================================================
-- VALUE-DESCRIPTION CARDINALITY (`max-value-descriptions-per-file`)
-- ============================================================================

-- Total value-description count summed across the three carriers:
-- per-signal `VAL_` entries, top-level `VAL_TABLE_` definitions, and
-- `unresolvedValueDescs` for VAL_ lines whose `(canId, signalName)` did
-- not resolve to a signal.  This sum is consulted against
-- `max-value-descriptions-per-file`.

vdsInSignals : List DBCSignal → ℕ
vdsInSignals [] = 0
vdsInSignals (s ∷ rest) = length (DBCSignal.valueDescriptions s) + vdsInSignals rest

vdsInMessages : List DBCMessage → ℕ
vdsInMessages [] = 0
vdsInMessages (m ∷ rest) = vdsInSignals (DBCMessage.signals m) + vdsInMessages rest

vdsInTables : List ValueTable → ℕ
vdsInTables [] = 0
vdsInTables (t ∷ rest) = length (ValueTable.entries t) + vdsInTables rest

vdsInUnresolved : List RawValueDesc → ℕ
vdsInUnresolved [] = 0
vdsInUnresolved (rv ∷ rest) = length (RawValueDesc.entries rv) + vdsInUnresolved rest

totalValueDescriptions : DBC → ℕ
totalValueDescriptions dbc =
  vdsInMessages (DBC.messages dbc) +
  vdsInTables (DBC.valueTables dbc) +
  vdsInUnresolved (DBC.unresolvedValueDescs dbc)

-- ============================================================================
-- STRING-LENGTH WALKS (`max-string-length-bytes`)
-- ============================================================================

-- Post-parse walks for every unbounded
-- `List Char` field.  Returns `nothing` if all fields are within bound,
-- else `(observed , limit)` for the first violation in discovery order.

firstOverBoundLC : List Char → Maybe (ℕ × ℕ)
firstOverBoundLC cs with length cs <ᵇ suc max-string-length-bytes
... | true  = nothing
... | false = just (length cs , max-string-length-bytes)

-- Walk a list of (ℕ , List Char) entries (value-description labels).
firstOverBoundEntries : List (ℕ × List Char) → Maybe (ℕ × ℕ)
firstOverBoundEntries [] = nothing
firstOverBoundEntries ((_ , cs) ∷ rest) with firstOverBoundLC cs
... | just over = just over
... | nothing   = firstOverBoundEntries rest

-- Walk per-signal: unit + value-description labels.
firstOverBoundSignal : DBCSignal → Maybe (ℕ × ℕ)
firstOverBoundSignal sig with firstOverBoundLC (DBCSignal.unit sig)
... | just over = just over
... | nothing   = firstOverBoundEntries (DBCSignal.valueDescriptions sig)

firstOverBoundInSignals : List DBCSignal → Maybe (ℕ × ℕ)
firstOverBoundInSignals [] = nothing
firstOverBoundInSignals (s ∷ rest) with firstOverBoundSignal s
... | just over = just over
... | nothing   = firstOverBoundInSignals rest

firstOverBoundInMessages : List DBCMessage → Maybe (ℕ × ℕ)
firstOverBoundInMessages [] = nothing
firstOverBoundInMessages (m ∷ rest) with firstOverBoundInSignals (DBCMessage.signals m)
... | just over = just over
... | nothing   = firstOverBoundInMessages rest

firstOverBoundInComments : List DBCComment → Maybe (ℕ × ℕ)
firstOverBoundInComments [] = nothing
firstOverBoundInComments (c ∷ rest) with firstOverBoundLC (DBCComment.text c)
... | just over = just over
... | nothing   = firstOverBoundInComments rest

firstOverBoundEnumLabels : List (List Char) → Maybe (ℕ × ℕ)
firstOverBoundEnumLabels [] = nothing
firstOverBoundEnumLabels (cs ∷ rest) with firstOverBoundLC cs
... | just over = just over
... | nothing   = firstOverBoundEnumLabels rest

firstOverBoundAttrType : AttrType → Maybe (ℕ × ℕ)
firstOverBoundAttrType (ATEnum vs) = firstOverBoundEnumLabels vs
firstOverBoundAttrType _           = nothing

firstOverBoundAttrValue : AttrValue → Maybe (ℕ × ℕ)
firstOverBoundAttrValue (AVString cs) = firstOverBoundLC cs
firstOverBoundAttrValue _             = nothing

firstOverBoundAttr : DBCAttribute → Maybe (ℕ × ℕ)
firstOverBoundAttr (DBCAttrDef ad) with firstOverBoundLC (AttrDef.name ad)
... | just over = just over
... | nothing   = firstOverBoundAttrType (AttrDef.attrType ad)
firstOverBoundAttr (DBCAttrDefault adef) with firstOverBoundLC (AttrDefault.name adef)
... | just over = just over
... | nothing   = firstOverBoundAttrValue (AttrDefault.value adef)
firstOverBoundAttr (DBCAttrAssign aa) with firstOverBoundLC (AttrAssign.name aa)
... | just over = just over
... | nothing   = firstOverBoundAttrValue (AttrAssign.value aa)

firstOverBoundInAttrs : List DBCAttribute → Maybe (ℕ × ℕ)
firstOverBoundInAttrs [] = nothing
firstOverBoundInAttrs (a ∷ rest) with firstOverBoundAttr a
... | just over = just over
... | nothing   = firstOverBoundInAttrs rest

firstOverBoundInValueTables : List ValueTable → Maybe (ℕ × ℕ)
firstOverBoundInValueTables [] = nothing
firstOverBoundInValueTables (vt ∷ rest) with firstOverBoundEntries (ValueTable.entries vt)
... | just over = just over
... | nothing   = firstOverBoundInValueTables rest

firstOverBoundInUnresolved : List RawValueDesc → Maybe (ℕ × ℕ)
firstOverBoundInUnresolved [] = nothing
firstOverBoundInUnresolved (rv ∷ rest) with firstOverBoundEntries (RawValueDesc.entries rv)
... | just over = just over
... | nothing   = firstOverBoundInUnresolved rest
