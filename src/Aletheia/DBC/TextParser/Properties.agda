-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Correctness properties for the DBC text-format parser: the facade its
-- proof layers are read through.
--
-- Each layer below is its own module, so one type-checks without the others
-- and an incremental rebuild pays for what changed; this module re-exports
-- them, so a consumer names one import. The layers run from the primitives an
-- identifier and a byte-order tag are parsed by, through the preamble, the
-- message topology, the value tables, the environment variables, the comments
-- and the signal groups, to the attribute section's dispatchers and the
-- char-class disjointness bridges the later layers rest on.
--
-- The universal statement those layers build toward,
--
--     parseText-on-formatText : ∀ d → WellFormedTextDBCAgg d
--                             → parseText (formatText d) ≡ inj₂ d
--
-- is not here: it needs `toList (fromList cs) ≡ cs`, which Agda's String
-- primitives do not give under `--safe --without-K`, since they reduce only on
-- closed terms, and which the standard library proves only in its own Unsafe
-- module. It is stated and proved in
-- `Aletheia.DBC.TextParser.Properties.Substrate.Unsafe`, the one module this
-- project allows to drop `--safe`, where the two bridging axioms and every
-- consumer of them sit together.
module Aletheia.DBC.TextParser.Properties where

-- Layer 2 — per-primitive roundtrips.  Identifier +
-- Tier A (byte-order / sign) + Tier B (string-literal escape body, mux
-- marker with embedded parseNatural).  `ATInt`/`ATFloat`/`ATHex`/
-- `ATEnum` and `SignalPresence` reclassified to Layer 3 (per-line-
-- construct payloads, not primitives).  The scope-tag / rel-scope /
-- ATString roundtrips were dropped — subsumed by the universal Format
-- DSL roundtrip in `Format/AttrDef.agda`.
open import Aletheia.DBC.TextParser.Properties.Primitives public
  using ( -- Probes + Identifier roundtrip
         -- Tier B — string literal (mux marker / bools sections below)
         )

-- Tier A primitives — extracted into `Properties.Primitives.Bools`.
-- Both functions are value-only single-char dispatchers; clean
-- self-contained extraction.
open import Aletheia.DBC.TextParser.Properties.Primitives.Bools public
  using ()

-- Tier B mux marker — extracted into `Properties.Primitives.MuxMarker`.
-- Imported here as a
-- sibling re-export to keep the public API surface stable for
-- downstream modules (Format/*, Properties/Aggregator/*,
-- Properties/Attributes/*, etc.) that read these names from
-- `Properties.agda` via the existing `open import Properties public`
-- chain.
open import Aletheia.DBC.TextParser.Properties.Primitives.MuxMarker public
  using ()

-- Layer 3 — per-line-construct roundtrips.  Preamble first; simple-
-- line, attribute, and message constructs follow.  See
-- `Properties/Preamble.agda` for the intra-section split.
open import Aletheia.DBC.TextParser.Properties.Preamble public
  using ()

-- Topology section: BU_ node list; the receiver list inside SG_ derived
-- from `Format.Receivers`, signal-line dispatchers derived from
-- `Format.SignalLine`; the SG_ block (`many parseSignalLine`) over a
-- list of DBCSignal under `WellFormedTextSignal`; `resolveSignalList`-
-- roundtrip recovering the original DBCSignal list from RawSignals under
-- MasterCoherent; the full `parseMessage`-roundtrip composer chaining the
-- DSL header, the SG_ block, manyHelper-parseNewline-exhaust, and
-- resolveSignalList.
open import Aletheia.DBC.TextParser.Properties.Topology public
  using ( -- list-level `many parseMessage` over BO_ blocks.
        )

-- Value-table section (VAL_TABLE_).
open import Aletheia.DBC.TextParser.Properties.ValueTables public
  using (-- list-level `many parseValueTable`.
         )

-- Environment-variable section (EV_).
open import Aletheia.DBC.TextParser.Properties.EnvVars public
  using (-- list-level `many parseEnvVar`.
         )

-- Comment section (CM_ — 5-way CommentTarget dispatch).
open import Aletheia.DBC.TextParser.Properties.Comments public
  using (-- list-level `many parseComment`.
         )

-- Signal-group section (Layer 3 carry-over — SignalGroup migrated to
-- Format DSL via `Format/SignalGroup.agda` + slim η-style wrap).  The
-- list-level lift follows.
open import Aletheia.DBC.TextParser.Properties.SignalGroups public
  using ()

-- Polymorphic `many-η-roundtrip` helper that lifts each per-element
-- η-style slim (the 5 simple sections above + the BO_ block) to its
-- list-level analogue.  Re-exported so Layer-4c composers pull a single
-- facade.
open import Aletheia.DBC.TextParser.Properties.ManyRoundtrip public
  using ()

-- Char-class disjointness: bridge lemmas the universal
-- aggregator owes to discharge each Layer 3 construct's `*NameStop`
-- precondition from `validIdentifierᵇ`.  Imported for re-export so
-- Layer 4b/c proofs can pull a single facade.
open import Aletheia.DBC.TextParser.Properties.CharClassDisjoint public
  using ()

-- Attribute section: BA_DEF_ + BA_DEF_REL_ and BA_DEF_DEF_; BA_ /
-- BA_REL_ and the top-level parseAttrLine 5-way <|> composer follow.
open import Aletheia.DBC.TextParser.Properties.Attributes public
  using ( -- Assign dispatchers — 5 standard × 3 + 2 rel × 3 = 21.
        -- parseAttrLine 5-way `<|>` composer — 31 dispatchers
        -- across alt1 (RawDef-Rel × 2 scopes), alt2 (RawDefault × 3
        -- shapes), alt3 (RawDef-NotRel × 5 scopes), alt4 (RawAssign-Rel
        -- × 6), alt5 (RawAssign × 15).
        )
