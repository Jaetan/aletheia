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
open import Data.Integer using (ℤ)
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

-- ============================================================================
-- NODE (DBC BU_ keyword)
-- ============================================================================

-- A network node (ECU) participating in the bus. The DBC BU_ line enumerates
-- these; senders on messages reference them by name.
record Node : Set where
  constructor mkNode
  field
    name : String

-- ============================================================================
-- COMMENT (DBC CM_ keyword family)
-- ============================================================================

-- Target of a DBC comment. Variants correspond to the DBC keyword
-- immediately after CM_: none (network-level), BU_ (node), BO_ (message),
-- SG_ (signal), EV_ (environment variable).
data CommentTarget : Set where
  CTNetwork : CommentTarget
  CTNode    : (node : String) → CommentTarget
  CTMessage : (msgID : CANId) → CommentTarget
  CTSignal  : (msgID : CANId) → (signal : String) → CommentTarget
  CTEnvVar  : (envVar : String) → CommentTarget

-- One DBC comment (a single CM_ line).
record DBCComment : Set where
  constructor mkComment
  field
    target : CommentTarget
    text   : String

-- ============================================================================
-- ATTRIBUTES (DBC BA_DEF_, BA_DEF_DEF_, BA_, BA_DEF_REL_, BA_REL_)
-- ============================================================================

-- Scope of an attribute *definition*.
-- Standard scopes (BA_DEF_): Network, Node, Message, Signal, EnvVar.
-- Relation scopes (BA_DEF_REL_): NodeMsg (BU_BO_REL_), NodeSig (BU_SG_REL_).
data AttrScope : Set where
  ASNetwork : AttrScope
  ASNode    : AttrScope
  ASMessage : AttrScope
  ASSignal  : AttrScope
  ASEnvVar  : AttrScope
  ASNodeMsg : AttrScope
  ASNodeSig : AttrScope

-- Declared type of an attribute value. INT and HEX carry integer bounds,
-- FLOAT carries rational bounds, STRING is unconstrained, and ENUM carries
-- the (ordered) list of enumeration labels.
data AttrType : Set where
  ATInt    : (min max : ℤ) → AttrType
  ATFloat  : (min max : ℚ) → AttrType
  ATString : AttrType
  ATEnum   : (values : List String) → AttrType
  ATHex    : (min max : ℕ) → AttrType

-- Concrete attribute value (BA_, BA_REL_, BA_DEF_DEF_).
-- AVEnum carries the 0-based index into the matching AttrDef's label list.
data AttrValue : Set where
  AVInt    : ℤ → AttrValue
  AVFloat  : ℚ → AttrValue
  AVString : String → AttrValue
  AVEnum   : ℕ → AttrValue
  AVHex    : ℕ → AttrValue

-- Assignment target (BA_ / BA_REL_). Mirrors AttrScope but carries the
-- concrete identifier(s) of the target entity.
data AttrTarget : Set where
  ATgtNetwork : AttrTarget
  ATgtNode    : (node : String) → AttrTarget
  ATgtMessage : (msgID : CANId) → AttrTarget
  ATgtSignal  : (msgID : CANId) → (signal : String) → AttrTarget
  ATgtEnvVar  : (envVar : String) → AttrTarget
  ATgtNodeMsg : (node : String) → (msgID : CANId) → AttrTarget
  ATgtNodeSig : (node : String) → (msgID : CANId) → (signal : String) → AttrTarget

-- BA_DEF_ / BA_DEF_REL_ — attribute type declaration.
record AttrDef : Set where
  constructor mkAttrDef
  field
    name     : String
    scope    : AttrScope
    attrType : AttrType

-- BA_DEF_DEF_ — default value for an attribute.
record AttrDefault : Set where
  constructor mkAttrDefault
  field
    name  : String
    value : AttrValue

-- BA_ / BA_REL_ — concrete attribute value assignment.
record AttrAssign : Set where
  constructor mkAttrAssign
  field
    name   : String
    target : AttrTarget
    value  : AttrValue

-- Unified attribute vocabulary: one constructor per DBC keyword family,
-- so a single `List DBCAttribute` preserves wire ordering across the five
-- BA_* keywords.
data DBCAttribute : Set where
  DBCAttrDef     : AttrDef     → DBCAttribute  -- BA_DEF_, BA_DEF_REL_
  DBCAttrDefault : AttrDefault → DBCAttribute  -- BA_DEF_DEF_
  DBCAttrAssign  : AttrAssign  → DBCAttribute  -- BA_, BA_REL_

record DBC : Set where
  field
    version : String
    messages : List DBCMessage
    signalGroups : List SignalGroup
    environmentVars : List EnvironmentVar
    valueTables : List ValueTable
    nodes : List Node
    comments : List DBCComment
    attributes : List DBCAttribute

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
  DuplicateAttributeName      : IssueCode
  UnknownCommentTarget        : IssueCode
  UnknownMessageSender        : IssueCode

-- A single validation issue
record ValidationIssue : Set where
  constructor mkIssue
  field
    severity : IssueSeverity
    code     : IssueCode
    detail   : String   -- Human-readable description
