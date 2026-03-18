{-# OPTIONS --safe --without-K #-}

-- DBC (Database CAN) file structure types.
--
-- Purpose: Define types representing DBC file contents (messages, signals, metadata).
-- Types: DBC (top-level), Message (CAN message definition), Signal (signal within message).
-- Role: Core data structure used throughout CAN processing and verification.
--
-- Design: Matches DBC file format with type-safe representations.
-- All numeric fields use ℕ for O(1) MAlonzo allocation.
module Aletheia.DBC.Types where

open import Aletheia.CAN.Frame using (CANId)
open import Aletheia.CAN.Signal using (SignalDef)
open import Aletheia.CAN.Endianness using (ByteOrder)
open import Data.String using (String)
open import Data.List using (List)
open import Data.Nat using (ℕ)

-- Signal presence model for multiplexing
-- A signal is either always present or conditionally present based on a multiplexor
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

record DBC : Set where
  field
    version : String
    messages : List DBCMessage

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

-- A single validation issue
record ValidationIssue : Set where
  constructor mkIssue
  field
    severity : IssueSeverity
    code     : IssueCode
    detail   : String   -- Human-readable description
