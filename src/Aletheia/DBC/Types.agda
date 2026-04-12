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

open import Aletheia.CAN.DLC using (DLC; dlcBytes)
open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Endianness using (ByteOrder)
open import Data.String using (String)
open import Data.List using (List)
open import Data.List.NonEmpty using (List⁺)
open import Data.Nat using (ℕ)
open import Data.Rational using (ℚ)
open import Data.Product using (_×_)

-- Signal presence model for multiplexing.
-- A signal is either always present or conditionally present based on a multiplexor.
--
-- Design: Models multiplexing with multi-value support and arbitrary nesting.
-- Each conditionally-present signal references one multiplexor signal and a
-- non-empty set of selector values (List⁺ ℕ). The signal is present when the
-- multiplexor's current value matches any element in the set.
--
-- The multiplexor signal may itself be conditionally present (nested mux).
-- The validator enforces acyclicity of the mux dependency graph; arbitrary
-- nesting depth is allowed up to length-of-signals.
--
-- This covers: standard DBC (single value), extended DBC SG_MUL_VAL_ (ranges
-- expanded to explicit values by cantools), multi-value selectors, and
-- nested multiplexing chains.
data SignalPresence : Set where
  Always : SignalPresence
  When : (multiplexor : String) → (values : List⁺ ℕ) → SignalPresence

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
    dlc : DLC
    sender : String
    signals : List DBCSignal

-- Signal group: named collection of signal references (DBC SG_ keyword).
record SignalGroup : Set where
  field
    name : String
    signals : List String

-- Environment variable type (DBC EV_ keyword varType field).
data VarType : Set where
  IntVar    : VarType  -- 0 in DBC specification
  FloatVar  : VarType  -- 1 in DBC specification
  StringVar : VarType  -- 2 in DBC specification

-- Encode VarType as ℕ for JSON serialization
varTypeToℕ : VarType → ℕ
varTypeToℕ IntVar    = 0
varTypeToℕ FloatVar  = 1
varTypeToℕ StringVar = 2

-- Environment variable (DBC EV_ keyword).
record EnvironmentVar : Set where
  field
    name : String
    varType : VarType
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
  MultiplexorCycle            : IssueCode
  GlobalNameCollision         : IssueCode
  MinExceedsMax               : IssueCode
  SignalExceedsDLC            : IssueCode
  SignalOverlap               : IssueCode
  BitLengthZero               : IssueCode
  DuplicateMessageName        : IssueCode
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
