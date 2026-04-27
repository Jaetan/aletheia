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
open import Data.Char using (Char)
open import Data.String using (String; fromList)
open import Data.List using (List)
open import Data.List.NonEmpty using (List⁺)
open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ)
open import Data.Rational using (ℚ)
open import Data.Product using (_×_)
open import Function using (_∘_)
open import Aletheia.DBC.DecRat using (DecRat)
open import Aletheia.DBC.DecRat.Refinement using (IntDecRat; NatDecRat)
open import Aletheia.DBC.Identifier using (Identifier)
open import Aletheia.DBC.CanonicalReceivers using (CanonicalReceivers)

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
  When : (multiplexor : Identifier) → (values : List⁺ ℕ) → SignalPresence

record DBCSignal : Set where
  field
    name : Identifier
    signalDef : SignalDef
    byteOrder : ByteOrder
    unit : List Char                 -- DBC unit literal; List Char post 3d.4 JSON-mirror
    presence : SignalPresence        -- Conditional presence for multiplexing
    receivers : CanonicalReceivers   -- Node names from SG_ trailing receiver list (3d.5.c-γ.2: refined to exclude singleton-Vector__XXX)

record DBCMessage : Set where
  field
    id : CANId
    name : Identifier
    dlc : DLC
    sender : Identifier              -- Primary transmitter from the BO_ line
    senders : List Identifier        -- Additional transmitters from BO_TX_BU_ lines
    signals : List DBCSignal

-- Signal group: named collection of signal references (DBC SG_ keyword).
record SignalGroup : Set where
  field
    name : Identifier
    signals : List Identifier

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
    name : Identifier
    varType : VarType
    initial : DecRat
    minimum : DecRat
    maximum : DecRat

-- Value description table (DBC VAL_TABLE_ keyword).
record ValueTable : Set where
  field
    name : Identifier
    entries : List (ℕ × List Char)  -- (numeric value, description) — List Char post 3d.4 JSON-mirror

-- ============================================================================
-- NODE (DBC BU_ keyword)
-- ============================================================================

-- A network node (ECU) participating in the bus. The DBC BU_ line enumerates
-- these; senders on messages reference them by name.
record Node : Set where
  constructor mkNode
  field
    name : Identifier

-- ============================================================================
-- COMMENT (DBC CM_ keyword family)
-- ============================================================================

-- Target of a DBC comment. Variants correspond to the DBC keyword
-- immediately after CM_: none (network-level), BU_ (node), BO_ (message),
-- SG_ (signal), EV_ (environment variable).
data CommentTarget : Set where
  CTNetwork : CommentTarget
  CTNode    : (node : Identifier) → CommentTarget
  CTMessage : (msgID : CANId) → CommentTarget
  CTSignal  : (msgID : CANId) → (signal : Identifier) → CommentTarget
  CTEnvVar  : (envVar : Identifier) → CommentTarget

-- One DBC comment (a single CM_ line).
record DBCComment : Set where
  constructor mkComment
  field
    target : CommentTarget
    text   : List Char  -- DBC comment body; List Char post 3d.4 JSON-mirror

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
  ATInt    : (min max : IntDecRat) → AttrType
  ATFloat  : (min max : DecRat) → AttrType
  ATString : AttrType
  ATEnum   : (values : List (List Char)) → AttrType  -- enum labels; List Char post 3d.4 JSON-mirror
  ATHex    : (min max : NatDecRat) → AttrType

-- Concrete attribute value (BA_, BA_REL_, BA_DEF_DEF_).
-- AVEnum carries the 0-based index into the matching AttrDef's label list.
data AttrValue : Set where
  AVInt    : IntDecRat → AttrValue
  AVFloat  : DecRat → AttrValue
  AVString : List Char → AttrValue  -- DBC string-attribute payload; List Char post 3d.4 JSON-mirror
  AVEnum   : NatDecRat → AttrValue
  AVHex    : NatDecRat → AttrValue

-- Assignment target (BA_ / BA_REL_). Mirrors AttrScope but carries the
-- concrete identifier(s) of the target entity.
data AttrTarget : Set where
  ATgtNetwork : AttrTarget
  ATgtNode    : (node : Identifier) → AttrTarget
  ATgtMessage : (msgID : CANId) → AttrTarget
  ATgtSignal  : (msgID : CANId) → (signal : Identifier) → AttrTarget
  ATgtEnvVar  : (envVar : Identifier) → AttrTarget
  ATgtNodeMsg : (node : Identifier) → (msgID : CANId) → AttrTarget
  ATgtNodeSig : (node : Identifier) → (msgID : CANId) → (signal : Identifier) → AttrTarget

-- BA_DEF_ / BA_DEF_REL_ — attribute type declaration.
-- `name` is a DBC wire-format quoted string literal (not restricted to the
-- identifier grammar).  Stored as `List Char` post 3d.4 JSON-mirror so the
-- JSON-side roundtrip stays axiom-free.
record AttrDef : Set where
  constructor mkAttrDef
  field
    name     : List Char
    scope    : AttrScope
    attrType : AttrType

-- BA_DEF_DEF_ — default value for an attribute.
record AttrDefault : Set where
  constructor mkAttrDefault
  field
    name  : List Char
    value : AttrValue

-- BA_ / BA_REL_ — concrete attribute value assignment.
record AttrAssign : Set where
  constructor mkAttrAssign
  field
    name   : List Char
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
    version : List Char  -- DBC VERSION header content; List Char post 3d.4 JSON-mirror
    messages : List DBCMessage
    signalGroups : List SignalGroup
    environmentVars : List EnvironmentVar
    valueTables : List ValueTable
    nodes : List Node
    comments : List DBCComment
    attributes : List DBCAttribute

-- ============================================================================
-- IDENTIFIER NAME ACCESSORS (convenience helpers — Identifier → String)
-- ============================================================================
-- After 3d.4 (2026-04-26) `Identifier.name : List Char`, so each accessor
-- composes `fromList` to recover the String.  Per-call cost is O(name-length)
-- and identifier names are <30 chars; not on the per-frame signal-extraction
-- hot path (called only at JSON serialization and validation sites).

signalNameStr : DBCSignal → String
signalNameStr = fromList ∘ Identifier.name ∘ DBCSignal.name

messageNameStr : DBCMessage → String
messageNameStr = fromList ∘ Identifier.name ∘ DBCMessage.name

messageSenderStr : DBCMessage → String
messageSenderStr = fromList ∘ Identifier.name ∘ DBCMessage.sender

nodeNameStr : Node → String
nodeNameStr = fromList ∘ Identifier.name ∘ Node.name

signalGroupNameStr : SignalGroup → String
signalGroupNameStr = fromList ∘ Identifier.name ∘ SignalGroup.name

envVarNameStr : EnvironmentVar → String
envVarNameStr = fromList ∘ Identifier.name ∘ EnvironmentVar.name

valueTableNameStr : ValueTable → String
valueTableNameStr = fromList ∘ Identifier.name ∘ ValueTable.name

-- Attribute names are free-form quoted strings in DBC wire format; post 3d.4
-- JSON-mirror they are stored as `List Char`, so each accessor composes
-- `fromList` to recover the String.
attrDefNameStr : AttrDef → String
attrDefNameStr = fromList ∘ AttrDef.name

attrDefaultNameStr : AttrDefault → String
attrDefaultNameStr = fromList ∘ AttrDefault.name

attrAssignNameStr : AttrAssign → String
attrAssignNameStr = fromList ∘ AttrAssign.name

-- ============================================================================
-- TEXT-TYPED FIELD ACCESSORS (post 3d.4 JSON-mirror — fields are List Char,
-- callers in String contexts can use these for `fromList ∘ field`)
-- ============================================================================

unitStr : DBCSignal → String
unitStr = fromList ∘ DBCSignal.unit

commentTextStr : DBCComment → String
commentTextStr = fromList ∘ DBCComment.text

versionStr : DBC → String
versionStr = fromList ∘ DBC.version

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
  UnknownSignalReceiver       : IssueCode

-- A single validation issue
record ValidationIssue : Set where
  constructor mkIssue
  field
    severity : IssueSeverity
    code     : IssueCode
    detail   : String   -- Human-readable description
