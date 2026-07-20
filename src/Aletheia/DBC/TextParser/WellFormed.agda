-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- DBC-level well-formedness predicate for the TEXT round-trip path.
--
-- Counterpart to `Aletheia.DBC.Formatter.WellFormed.WellFormedDBC` (the
-- 1-field JSON-side companion of `WellFormedDBCRT`).  Asymmetry is by
-- design, not under-specification:
--
--   * JSON-side `WellFormedDBC` (and its strengthening `WellFormedDBCRT`)
--     is the precondition for `parseDBCWithErrors ∘ formatDBC ≡ id` on
--     the JSON wire.  All metadata (signal groups, env vars, value
--     tables, nodes, comments, attributes, unresolved value descs)
--     round-trips through JSON without additional preconditions
--     because every field type either parses unconditionally
--     (rationals, naturals, identifier-validated strings) or carries
--     its constraint at the type level.
--
--   * Text-side `WellFormedTextDBCAgg` (this record) is the precondition
--     for `parseText ∘ formatText ≡ id` on the DBC text wire.  Text
--     emission is materially lossier than JSON: the formatter does not
--     emit `BO_TX_BU_` (per-message extra senders), normalises
--     `Vector__XXX` placeholders, drops multi-value mux selectors, and
--     gives no canonical text representation for orphan
--     `unresolvedValueDescs` entries.  Each lossy region is reflected
--     here as an explicit field: section-level `*Stop` predicates,
--     `MessageWF`, `WFAttribute`, `SignalGroupWF`, cross-message CAN-ID
--     uniqueness, and an `unresolvedValueDescs ≡ []` constraint.
--
-- Formerly defined inline in
-- `Aletheia.DBC.TextParser.Properties.Aggregator.Universal` under the
-- name `WellFormedDBC`.  It was extracted here:
--   * naming collision with the JSON-side `WellFormedDBC` resolved by
--     renaming this record to `WellFormedTextDBCAgg` (the suffix `Agg`
--     marks it as the universal-aggregator predicate, distinct from
--     the now-removed 1-field stub `Formatter.WellFormedText.
--     WellFormedTextDBC`);
--   * the type definition is now separated from the universal theorem
--     (`Aggregator.Universal.parseTextChars-on-formatChars`) per the
--     module-organisation guideline.
--
-- A companion obligation (the FormatDBCText FFI handler must discharge
-- `WellFormedTextDBCAgg` at runtime) is tracked separately as a
-- deferral.
module Aletheia.DBC.TextParser.WellFormed where

open import Data.List using ([]; map)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Aletheia.DBC.Types using
  ( DBC; DBCMessage )

-- Per-section preconditions.
open import Aletheia.DBC.TextParser.Properties.ValueTables using
  (ValueTableNameStop)
open import Aletheia.DBC.TextParser.Properties.Topology using
  (MessageWF; NodeNameStop)
open import Aletheia.DBC.TextParser.Properties.EnvVars using
  (EnvVarNameStop)
open import Aletheia.DBC.TextParser.Properties.Comments using
  (CommentTargetStop)
open import Aletheia.DBC.TextParser.Properties.SignalGroups using
  (SignalGroupWF)

-- Attribute-side precondition.  `WFAttribute` references
-- `collectDefs (DBC.attributes d)` so the `attr-wfs` field carries
-- the BA_DEF_ context against which BA_ assigns are typed.
open import Aletheia.DBC.TextParser.Properties.Aggregator.Foundations using
  (WFAttribute)
open import Aletheia.DBC.TextFormatter.Attributes using
  (collectDefs)


-- ============================================================================
-- AGGREGATOR PREDICATE
-- ============================================================================
--
-- Bundles every per-section precondition the text universal roundtrip
-- needs.  Each field is the same predicate the matching Layer 3 / 4
-- per-construct slim takes.
--
-- Membership is decidable at runtime, soundly and completely:
-- `wfTextIssues d ≡ [] ⟺ WellFormedTextDBCAgg d`
-- (`Properties.WellFormedCheck.Sound`).  DBC validity does NOT imply this
-- predicate — text emission is lossy on constructs the validator accepts —
-- and no runtime guarantee depends on that implication; see the
-- `Properties.WellFormedFromValidity` module header for the counterexample
-- class and the two results that carry the guarantee instead.

record WellFormedTextDBCAgg (d : DBC) : Set where
  field
    node-stops : All NodeNameStop                                   (DBC.nodes           d)
    vt-stops   : All ValueTableNameStop                             (DBC.valueTables     d)
    msg-wfs    : All MessageWF                                      (DBC.messages        d)
    ev-stops   : All EnvVarNameStop                                 (DBC.environmentVars d)
    cm-stops   : All CommentTargetStop                              (DBC.comments        d)
    attr-wfs   : All (WFAttribute (collectDefs (DBC.attributes d))) (DBC.attributes      d)
    sg-wfs     : All SignalGroupWF                                  (DBC.signalGroups    d)
    -- Cross-message CAN-ID uniqueness.  Required by
    -- `attachValueDescs ∘ collectFromMessages ≡ id` (the inverse-bridge
    -- in `Properties.Aggregator.Refine.ValueDescriptions`): two distinct
    -- messages with the same CAN ID would have their per-signal VAL_
    -- entries collapse onto whichever message `lookup-vd` finds first,
    -- breaking the round-trip.  The same first-match collapse runs through a
    -- second id-keyed channel: `BO_TX_BU_` message senders re-attach via
    -- `lookup-senders` (keyed on the CAN id alone), so duplicate ids also
    -- collapse divergent sender lists onto the first match.  Validator's
    -- CHECK 1 (`DuplicateMessageId`, an error-class check) enforces this at
    -- DBC-load time.
    msg-ids-unique : AllPairs _≢_ (map DBCMessage.id (DBC.messages d))
    -- `formatText` does not emit lines for
    -- `DBC.unresolvedValueDescs` entries (no canonical text representation
    -- — they could be re-emitted as VAL_ lines but those would be silently
    -- re-collected as unresolved on parse-back, leaving the round-trip
    -- closed but lossy).  The text round-trip therefore closes only for
    -- DBCs whose unresolved list is already `[]`; this includes every
    -- DBC built from `parseText` (because `unresolvedRVDs ∘ collectFrom
    -- Messages ≡ []` under any `msgs`) and every JSON-built DBC whose
    -- wire omits the `unresolvedValueDescs` key (absent-key default
    -- `[]`; a supplied non-empty array is preserved).  CHECK 23
    -- `UnknownValueDescriptionTarget` warns at validation time when
    -- this field is non-empty (E.11).
    unresolved-empty : DBC.unresolvedValueDescs d ≡ []
