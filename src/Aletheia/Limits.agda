{-# OPTIONS --safe --without-K #-}

-- Adversarial-input bounds at parser surfaces.
--
-- Purpose: Single source of truth for the compile-time bound constants
-- enforced by every parser at a trust boundary (DBC text, JSON at the
-- FFI boundary, binary frame decoder, attribute / value-table inputs,
-- YAML / Excel loaders).  Per AGENTS.md universal rule "Adversarial-input
-- bounds at parser surfaces", rejection over the bound is a typed error
-- (`InputBoundExceeded`) carrying the offending kind, observed value, and
-- the limit it crossed.
--
-- Cross-references:
--   * docs/architecture/PROTOCOL.md § Limits — wire-side documentation.
--   * Aletheia.Error — `InputBoundExceeded` constructors (ParseError,
--     DBCTextParseError, FrameError).
--   * Each binding mirrors `InputBoundExceededError` at the FFI entry
--     to short-circuit before marshaling: Python aletheia.exceptions,
--     Go *aletheia.InputBoundExceededError, C++ aletheia::InputBoundExceededError.
--
-- Rationale for values:
--   * 64 MiB input — commercial automotive DBCs are 1-10 MiB; 6× headroom.
--   * 64 nesting depth — matches nlohmann/json default.
--   * 10k messages, 1024 signals/message — frame-bit count caps real
--     signal counts much earlier; cardinality is the OOM defense, not a
--     design constraint.
--   * 1M value descriptions — VAL_/VAL_TABLE_ entries can fan out across
--     many enum-typed signals; generous to avoid rejecting legitimate DBCs.
--   * 128-char identifiers — DBC convention is 32; 4× headroom.
--   * 64 KiB string body — comments, attribute string values.
--   * 1024 atoms/property — LTL property atom complexity.
--   * 64-byte frame — CAN-FD maximum payload.
module Aletheia.Limits where

open import Data.Nat using (ℕ)
open import Data.String using (String)

-- ============================================================================
-- BOUND KIND ENUM
-- ============================================================================

-- Discriminator for the kind of bound that was crossed.  Each accepting
-- error ADT (ParseError, DBCTextParseError, FrameError) wraps a
-- `BoundKind` plus the observed value and the canonical limit, so a
-- single canonical wire string per kind can be emitted by `boundKindCode`.
data BoundKind : Set where
  -- Total input length in bytes (parser entry).
  InputLengthBytes        : BoundKind
  -- JSON nesting depth (object / array containment).
  NestingDepth            : BoundKind
  -- List cardinality at any single level (signals, messages,
  -- attributes, value descriptions, ...).
  ArrayCardinality        : BoundKind
  -- Identifier-grammar string length (DBC names).
  IdentifierLength        : BoundKind
  -- Quoted-string body length (comments, attribute string values).
  StringLength            : BoundKind
  -- LTL atom count per property.
  AtomCount               : BoundKind
  -- CAN frame byte count (8 for CAN 2.0B, 64 for CAN-FD).
  FrameByteCount          : BoundKind
  -- Number of properties submitted in one `setProperties` call.
  PropertyCount           : BoundKind

boundKindCode : BoundKind → String
boundKindCode InputLengthBytes  = "input_length_bytes"
boundKindCode NestingDepth      = "nesting_depth"
boundKindCode ArrayCardinality  = "array_cardinality"
boundKindCode IdentifierLength  = "identifier_length"
boundKindCode StringLength      = "string_length"
boundKindCode AtomCount         = "atom_count"
boundKindCode FrameByteCount    = "frame_byte_count"
boundKindCode PropertyCount     = "property_count"

boundKindLabel : BoundKind → String
boundKindLabel InputLengthBytes  = "input length (bytes)"
boundKindLabel NestingDepth      = "nesting depth"
boundKindLabel ArrayCardinality  = "array cardinality"
boundKindLabel IdentifierLength  = "identifier length"
boundKindLabel StringLength      = "string length"
boundKindLabel AtomCount         = "atom count"
boundKindLabel FrameByteCount    = "frame byte count"
boundKindLabel PropertyCount     = "property count"

-- ============================================================================
-- BOUND CONSTANTS
-- ============================================================================

-- Total DBC-text input length in bytes.
max-dbc-text-bytes : ℕ
max-dbc-text-bytes = 67108864      -- 64 MiB = 64 × 1024 × 1024

-- Total JSON input length in bytes (FFI boundary).
max-json-bytes : ℕ
max-json-bytes = 67108864          -- 64 MiB

-- JSON object/array nesting depth.
max-nesting-depth : ℕ
max-nesting-depth = 64

-- DBC messages per file.
max-messages-per-file : ℕ
max-messages-per-file = 10000

-- Signals per single DBC message.
max-signals-per-message : ℕ
max-signals-per-message = 1024

-- Attribute definitions / assignments per DBC file.
max-attributes-per-file : ℕ
max-attributes-per-file = 10000

-- Value-description entries per DBC file (VAL_ + VAL_TABLE_), counted
-- as the SUM across `DBCSignal.valueDescriptions`, `ValueTable.entries`,
-- and `DBC.unresolvedValueDescs.entries`.  The 64 MiB input cap already
-- protects against the largest fan-outs; this bound is the explicit
-- cardinality gate at the handler boundary.
max-value-descriptions-per-file : ℕ
max-value-descriptions-per-file = 1000000

-- Comments per DBC file (`CM_`).  10k matches `max-attributes-per-file`
-- as the metadata-cap convention; real DBCs are well under.
max-comments-per-file : ℕ
max-comments-per-file = 10000

-- Nodes per DBC file (`BU_`).  Real DBCs have <200 nodes; 10k is
-- generous headroom matching the metadata-cap convention.
max-nodes-per-file : ℕ
max-nodes-per-file = 10000

-- Value-table definitions per DBC file (`VAL_TABLE_`).  The per-file
-- count, NOT the per-table entry count — that flows through
-- `max-value-descriptions-per-file`.
max-value-tables-per-file : ℕ
max-value-tables-per-file = 10000

-- DBC identifier (signal name, message name, etc.) length in characters.
max-identifier-length : ℕ
max-identifier-length = 128

-- Quoted-string body (comment text, attribute string value) length in bytes.
max-string-length-bytes : ℕ
max-string-length-bytes = 65536    -- 64 KiB

-- LTL atoms per single property.
max-atom-count-per-property : ℕ
max-atom-count-per-property = 1024

-- CAN frame payload byte count (CAN-FD maximum).
max-frame-byte-count : ℕ
max-frame-byte-count = 64

-- LTL properties submittable in one `setProperties` call.  1024 is
-- symmetric with `max-atom-count-per-property`; real-world CAN
-- analyses run 1-50 properties per stream so this is ~20x headroom.
max-properties-per-stream : ℕ
max-properties-per-stream = 1024

