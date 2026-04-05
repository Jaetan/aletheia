{-# OPTIONS --safe --without-K #-}

-- DBC (Database CAN) file structure types.
--
-- Purpose: Define types representing DBC file contents (messages, signals, metadata).
-- Types: DBC (top-level), Message (CAN message definition), Signal (signal within message).
-- Role: Core data structure used throughout CAN processing and verification.
--
-- Design: Represents DBC file content semantically with type-safe fields.
-- All numeric fields use ℕ for O(1) MAlonzo allocation.
module Aletheia.DBC.Types where

open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Endianness using (ByteOrder)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Data.Rational using (ℚ)
open import Data.Product using (_×_)

-- Signal presence model for multiplexing.
-- A signal is either always present or conditionally present based on a multiplexor.
--
-- Design: Models single-level multiplexing as defined by the DBC file format.
-- Each conditionally-present signal references exactly one multiplexor signal
-- and one selector value.
--
-- Limitations (by design):
--   - Nested multiplexing (mux of mux) is not representable.
--   - Range-based multiplexing (signal present for mux values 1–5) is not representable.
--   - These limitations match the standard DBC format; supporting them would require
--     a recursive or range-based presence type, cascading through 34+ modules.
data SignalPresence : Set where
  Always : SignalPresence
  When : (multiplexor : String) → (value : ℕ) → SignalPresence

record DBCSignal : Set where
  field
    name : String
    signalDef : SignalDef
    byteOrder : ByteOrder
    unit : String
    presence : SignalPresence  -- Conditional presence for multiplexing

record DBCMessage : Set where
  field
    id : CANId
    name : String
    dlc : ℕ
    sender : String
    signals : List DBCSignal

-- Signal group: named collection of signal references (DBC SG_ keyword).
record SignalGroup : Set where
  field
    name : String
    signals : List String

-- Environment variable (DBC EV_ keyword).
record EnvironmentVar : Set where
  field
    name : String
    varType : ℕ        -- 0 = integer, 1 = float, 2 = string
    initial : ℚ
    minimum : ℚ
    maximum : ℚ

-- Value description table (DBC VAL_TABLE_ keyword).
record ValueTable : Set where
  field
    name : String
    entries : List (ℕ × String)  -- (numeric value, description)

record DBC : Set where
  field
    version : String
    messages : List DBCMessage
    signalGroups : List SignalGroup
    environmentVars : List EnvironmentVar
    valueTables : List ValueTable

-- ============================================================================
-- VALIDATION ISSUE TYPES
-- ============================================================================

-- Severity of a validation issue
data IssueSeverity : Set where
  IsError   : IssueSeverity
  IsWarning : IssueSeverity

-- Structural codes for validation issues (type-safe enum, not stringly-typed)
data IssueCode : Set where
  DuplicateMessageId          : IssueCode
  DuplicateSignalName         : IssueCode
  FactorZero                  : IssueCode
  MultiplexorNotFound         : IssueCode
  MultiplexorNotAlwaysPresent : IssueCode
  GlobalNameCollision         : IssueCode
  MinExceedsMax               : IssueCode
  SignalExceedsDLC            : IssueCode
  SignalOverlap               : IssueCode
  BitLengthZero               : IssueCode
  DuplicateMessageName        : IssueCode
  DLCOutOfRange               : IssueCode
  OffsetScaleRange            : IssueCode
  EmptyMessage                : IssueCode
  StartBitOutOfRange          : IssueCode
  BitLengthExcessive          : IssueCode
  MultiplexorNonUnitScaling   : IssueCode

-- A single validation issue
record ValidationIssue : Set where
  constructor mkIssue
  field
    severity : IssueSeverity
    code     : IssueCode
    detail   : String   -- Human-readable description
