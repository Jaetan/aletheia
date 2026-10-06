-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Adversarial-input bounds at parser surfaces.
--
-- Purpose: Single source of truth for the compile-time bound constants
-- enforced by every parser at a trust boundary (DBC text, JSON at the
-- FFI boundary, attribute / value-table inputs, YAML / Excel loaders).  Per
-- AGENTS.md universal rule "Adversarial-input bounds at parser surfaces",
-- rejection over the bound is a typed error (`InputBoundExceeded`)
-- carrying the offending kind, observed value, and the limit it crossed.
-- The binary frame decoder needs no constant here: the C ABI's `uint8_t`
-- `data_len` caps what it reads at 255 bytes, and `CAN.Frame.Parse` refuses
-- any payload whose length is not the DLC's.
--
-- Cross-references:
--   * docs/architecture/PROTOCOL.md § Limits — wire-side documentation.
--   * Aletheia.Error — the `InputBoundExceeded` constructor of `Error`.
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
--   * 65,536-character text fields — comments, attribute string values.
--   * 1024 atoms/property — LTL property atom complexity.
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
  -- Number of properties submitted in one `setProperties` call.
  PropertyCount           : BoundKind
  -- Magnitude of a JSON number's rational components (|numerator| and
  -- denominator of the exact ℚ a JSON number literal or
  -- {"numerator", "denominator"} object component denotes).
  RationalComponentMagnitude : BoundKind

boundKindCode : BoundKind → String
boundKindCode InputLengthBytes  = "input_length_bytes"
boundKindCode NestingDepth      = "nesting_depth"
boundKindCode ArrayCardinality  = "array_cardinality"
boundKindCode IdentifierLength  = "identifier_length"
boundKindCode StringLength      = "string_length"
boundKindCode AtomCount         = "atom_count"
boundKindCode PropertyCount     = "property_count"
boundKindCode RationalComponentMagnitude = "rational_component_magnitude"

boundKindLabel : BoundKind → String
boundKindLabel InputLengthBytes  = "input length (bytes)"
boundKindLabel NestingDepth      = "nesting depth"
boundKindLabel ArrayCardinality  = "array cardinality"
boundKindLabel IdentifierLength  = "identifier length"
boundKindLabel StringLength      = "string length"
boundKindLabel AtomCount         = "atom count"
boundKindLabel PropertyCount     = "property count"
boundKindLabel RationalComponentMagnitude = "rational component magnitude"

-- ============================================================================
-- BOUND CONSTANTS
-- ============================================================================

-- A DBC text file's length in bytes, the bindings' cap on a file or text
-- they read; the kernel receives a DBC text inside a JSON command, which
-- `max-json-bytes` bounds.
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
-- and `DBC.unresolvedValueDescs.entries`.
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

-- Signal groups per DBC file (`SIG_GROUP_`), at the metadata-cap
-- convention.  A group's members are one message's signals, so they are
-- bounded by `max-signals-per-message`.
max-signal-groups-per-file : ℕ
max-signal-groups-per-file = 10000

-- Environment variables per DBC file (`EV_`), at the metadata-cap
-- convention.
max-environment-variables-per-file : ℕ
max-environment-variables-per-file = 10000

-- `VAL_` lines per DBC file naming no signal of the file, counted as
-- lines: their entries flow through `max-value-descriptions-per-file`.
max-unresolved-value-descriptions-per-file : ℕ
max-unresolved-value-descriptions-per-file = 10000

-- Labels of one enumerated attribute type (`BA_DEF_ … ENUM`), at the
-- metadata-cap convention.
max-enum-labels-per-attribute : ℕ
max-enum-labels-per-attribute = 10000

-- Selector values one multiplexed signal is present for.
max-multiplex-values-per-signal : ℕ
max-multiplex-values-per-signal = 1024

-- DBC identifier (signal name, message name, etc.) length in characters.
max-identifier-length : ℕ
max-identifier-length = 128

-- A DBC text field (version, unit, comment, attribute name or value, value
-- label) length in characters.
max-string-length-characters : ℕ
max-string-length-characters = 65536

-- LTL atoms per single property.
max-atom-count-per-property : ℕ
max-atom-count-per-property = 1024

-- LTL properties submittable in one `setProperties` call.  1024 is
-- symmetric with `max-atom-count-per-property`; real-world CAN
-- analyses run 1-50 properties per stream so this is ~20x headroom.
max-properties-per-stream : ℕ
max-properties-per-stream = 1024

-- Magnitude cap on every JSON number's rational components: |numerator|
-- and denominator of the exact ℚ each number denotes, measured on the
-- parsed (reduced) form.  2^63 - 1 — the signed 64-bit wire range that
-- the binary FFI's rational slots and the decimal SSOT
-- (`aletheia_parse_decimal`, Int64-checked at the marshaling boundary)
-- already enforce; the JSON wire enforces the same range so a bare
-- integer cannot smuggle an unrepresentable component past the typed
-- decimal path.  Magnitude formulation: the single Int64 value with
-- magnitude 2^63 (numerator -2^63) is refused here even though the
-- binary wire could carry it, keeping one symmetric limit in the
-- structured `observed` / `limit` wire triple.
max-rational-component-magnitude : ℕ
max-rational-component-magnitude = 9223372036854775807

