{-# OPTIONS --safe --without-K #-}

-- Correctness properties for the DBC text-format parser — facade
-- placeholder (Phase B.3.b).
--
-- Purpose: Top-level theorem module for `Aletheia.DBC.TextParser`.  The
-- split-from-day-one structure follows the `DBC/Formatter/` facade
-- pattern (see feedback_properties_facade_split.md): each sub-file
-- type-checks independently, which keeps incremental rebuild cost low
-- once the proof burden grows past the ~600–800 line soft cap.
--
-- Planned sub-files (populated in B.3.c → B.3.d as each proof layer
-- lands):
--   * Aletheia.DBC.TextParser.Grammar.agda          — grammar well-
--     formedness: no-trailing-whitespace invariants, keyword
--     disjointness, lexer-vs-grammar agreement lemmas.
--   * Aletheia.DBC.TextParser.VersionRoundtrip.agda — parseText on
--     `VERSION/NS_/BS_` preamble recovers the original DBC preamble
--     (first grammar category, anchors the roundtrip base case).
--   * Aletheia.DBC.TextParser.MessageRoundtrip.agda — BO_/SG_ roundtrip,
--     mirroring DBC/Formatter/MessageRoundtrip.agda's shape.
--   * Aletheia.DBC.TextParser.MetadataRoundtrip.agda — CM_/BA_*/VAL_*/
--     SIG_GROUP_/SIG_VALTYPE_/SG_MUL_VAL_/EV_ roundtrip, mirroring
--     DBC/Formatter/MetadataRoundtrip.agda.
--   * Aletheia.DBC.TextParser.ErrorCompleteness.agda — every
--     `DBCTextParseError` constructor is reachable from at least one
--     malformed-input witness (no dead error codes).
--
-- Facade contract (B.3.d): this module will `open import ... public
-- using (...)` each sub-file's proved lemmas and expose the top-level
-- `parseText-formatText-roundtrip : ∀ d → parseText (formatText d) ≡
-- inj₂ d`.  For B.3.b the module body is intentionally empty — the
-- sub-files don't exist yet and creating placeholder holes would flag
-- spuriously under `check-properties`.
--
-- Pre-implementation audit (2026-04-22, pre-layer-1).  The stdlib
-- substrate audit mandated by PARITY_PLAN.md §B.3.d is complete.
-- Finding: the layer-1 target lemma
--
--     toList-++ₛ : ∀ s t → toList (s ++ₛ t) ≡ toList s ++ₗ toList t
--
-- (plus `toList-fromList` and `fromList-toList`) exists in stdlib only
-- via `Data.String.Unsafe`, where it is proven by `trustMe` under
-- `{-# OPTIONS --with-K #-}`.  That module is labelled Unsafe and
-- cannot be imported from a `--safe` module.  `Data.String.Properties`
-- and `Agda.Builtin.String.Properties` carry no append-behaviour
-- lemma at any layer.  Under `--safe --without-K`, the Agda String
-- primitives (`primStringAppend`, `primStringToList`,
-- `primStringFromList`) only reduce on closed terms, so a direct
-- in-project proof is also blocked.
--
-- Consequence: layer 1 is **not** import-and-re-export.  Four options
-- are enumerated in `project_b3d_stdlib_audit.md`; selecting one
-- requires explicit user approval — do NOT silently introduce an
-- Unsafe module (`feedback_no_suppression_without_approval.md`) or
-- silently weaken the target (`feedback_no_silent_proof_reframing.md`).
module Aletheia.DBC.TextParser.Properties where

-- Layer 2 — per-primitive roundtrips.  Identifier (commit 2b) +
-- Tier A (byte-order / sign) + Tier B (string-literal escape body, mux
-- marker with embedded parseNatural).  `ATInt`/`ATFloat`/`ATHex`/
-- `ATEnum` and `SignalPresence` reclassified to Layer 3 (per-line-
-- construct payloads, not primitives — see `memory/project_b3d_
-- universal_proof.md`).  Post-3d.5.d 3c-A, the scope-tag / rel-scope /
-- ATString roundtrips were dropped — subsumed by the universal Format
-- DSL roundtrip in `Format/AttrDef.agda`.
open import Aletheia.DBC.TextParser.Properties.Primitives public
  using ( -- Probes + Identifier roundtrip
         parseIdentifier-roundtrip;
         mkIdentFromChars-on-valid;
         decompose-valid;
         satisfy-success-T;
         buildIdent-eq;
         -- Tier A primitives
         parseByteOrderDigit-roundtrip;
         parseSignFlag-roundtrip;
         -- Tier B primitives
         parseStringLit-roundtrip;
         parseMuxMarker-IsMux-roundtrip;
         parseMuxMarker-left-branch;
         parseMuxMarker-NotMux-roundtrip;
         parseMuxMarker-SelBy-roundtrip)

-- Layer 3 — per-line-construct roundtrips.  Preamble first (Commit
-- 3a); simple-line, attribute, message constructs cascade in 3b / 3c /
-- 3d.  See `memory/project_b3d_universal_proof.md` for the partition
-- and `Properties/Preamble.agda` for the intra-commit split.
open import Aletheia.DBC.TextParser.Properties.Preamble public
  using (isNewlineStart;
         parseNewline-match-LF;
         parseNewline-fail-on-stop;
         manyHelper-parseNewline-exhaust;
         manyHelper-one-iter;
         many-parseNewline-one-LF-stop;
         parseVersion-roundtrip;
         parseBitTiming-roundtrip;
         parseNamespace-roundtrip;
         isNSLineStart)

-- Topology section (Commit 3b: BU_ node list; Commit 3d.5.c-η: receiver
-- list inside SG_ derived from `Format.Receivers`, signal-line
-- dispatchers derived from `Format.SignalLine`; Commit 3d.6: SG_ block
-- (`many parseSignalLine`) over a list of DBCSignal under
-- `WellFormedTextSignal`; Commit 3d.7: `resolveSignalList`-roundtrip
-- recovering the original DBCSignal list from RawSignals under
-- MasterCoherent; Commit 3d.8: full `parseMessage`-roundtrip composer
-- chaining DSL header + 3d.6 + manyHelper-parseNewline-exhaust + 3d.7).
open import Aletheia.DBC.TextParser.Properties.Topology public
  using ( parseBU-roundtrip; NodeNameStop
        ; isReceiverCont
        ; emit-canonicalReceiversFmt-eq-emitReceivers
        ; SignalNameStop; expectedRaw
        ; parseSignalLine-roundtrip-NotMux
        ; parseSignalLine-roundtrip-IsMux
        ; parseSignalLine-roundtrip-SelBy
        ; SignalLineWF
        ; expectedMux; expectedMuxFor; expectedRawOfDBC
        ; parseSignalLines-roundtrip
        ; SigOK; sigok-always; sigok-when
        ; resolveSignalList-roundtrip
        ; IdentHeadNonHSpace
        ; emitMessage-chars-decompose
        ; messageHeader-roundtrip
        ; buildMessage-roundtrip
        ; parseMessage-roundtrip
        -- 4b: list-level `many parseMessage` over BO_ blocks.
        ; MessageWF; parseMessage-roundtrip-bundled
        ; signalLineFmt-fails-on-newline
        ; parseMessages-roundtrip)

-- Value-table section (Commit 3b: VAL_TABLE_).
open import Aletheia.DBC.TextParser.Properties.ValueTables public
  using (parseValueTable-roundtrip; ValueTableNameStop;
         -- 4b: list-level `many parseValueTable`.
         parseValueTables-roundtrip)

-- Environment-variable section (Commit 3b: EV_).
open import Aletheia.DBC.TextParser.Properties.EnvVars public
  using (parseEnvVar-roundtrip; EnvVarNameStop;
         -- 4b: list-level `many parseEnvVar`.
         parseEnvVars-roundtrip)

-- Comment section (Commit 3b: CM_ — 5-way CommentTarget dispatch).
open import Aletheia.DBC.TextParser.Properties.Comments public
  using (parseComment-roundtrip; CommentTargetStop;
         -- 4b: list-level `many parseComment`.
         parseComments-roundtrip)

-- Signal-group section (Commit 4a: Layer 3 carry-over — SignalGroup
-- migrated to Format DSL via `Format/SignalGroup.agda` + slim η-style
-- wrap).  4b adds list-level lift.
open import Aletheia.DBC.TextParser.Properties.SignalGroups public
  using (parseSignalGroup-roundtrip; SignalGroupNameStop; SigNameStop;
         SignalGroupWF; parseSignalGroups-roundtrip)

-- 4b: polymorphic `many-η-roundtrip` helper that lifts each per-element
-- η-style slim (the 5 simple sections above + the BO_ block) to its
-- list-level analogue.  Re-exported so Layer-4c composers pull a single
-- facade.
open import Aletheia.DBC.TextParser.Properties.ManyRoundtrip public
  using (many-η-roundtrip)

-- Char-class disjointness (Commit 4a): bridge lemmas the universal
-- aggregator owes to discharge each Layer 3 construct's `*NameStop`
-- precondition from `validIdentifierᵇ`.  Imported for re-export so
-- Layer 4b/c proofs can pull a single facade.
open import Aletheia.DBC.TextParser.Properties.CharClassDisjoint public
  using (isIdentStart→¬isHSpace;
         isIdentCont→¬isHSpace;
         isIdentCont→¬isNewlineStart;
         showInt-chars-head-non-hspace)

-- Attribute section (Commit 3c.1: BA_DEF_ + BA_DEF_REL_; Commit 3c.2:
-- BA_DEF_DEF_).  Future 3c.3–3c.4 land BA_/BA_REL_ and the top-level
-- parseAttrLine 5-way <|> composer.
open import Aletheia.DBC.TextParser.Properties.Attributes public
  using ( WfAttrType; WfATInt; WfATFloat; WfATString; WfATEnum; WfATHex
        ; WfAttrDef-NotRel; Wf-Network; Wf-Node; Wf-Message; Wf-Signal; Wf-EnvVar
        ; WfAttrDef-Rel;    Wf-NodeMsg; Wf-NodeSig
        ; IdentNameStop
        ; parseAttrDef-roundtrip
        ; parseAttrDefRel-roundtrip
        ; parseRawAttrDefault-roundtrip-RavString
        ; parseRawAttrDefault-roundtrip-RavDecRatFrac
        ; parseRawAttrDefault-roundtrip-RavDecRatBareInt
        -- Assign dispatchers (3c.3) — 5 standard × 3 + 2 rel × 3 = 21.
        ; parseRawAttrAssign-roundtrip-ATgtNetwork-RavString
        ; parseRawAttrAssign-roundtrip-ATgtNetwork-RavDecRatFrac
        ; parseRawAttrAssign-roundtrip-ATgtNetwork-RavDecRatBareInt
        ; parseRawAttrAssign-roundtrip-ATgtNode-RavString
        ; parseRawAttrAssign-roundtrip-ATgtNode-RavDecRatFrac
        ; parseRawAttrAssign-roundtrip-ATgtNode-RavDecRatBareInt
        ; parseRawAttrAssign-roundtrip-ATgtMessage-RavString
        ; parseRawAttrAssign-roundtrip-ATgtMessage-RavDecRatFrac
        ; parseRawAttrAssign-roundtrip-ATgtMessage-RavDecRatBareInt
        ; parseRawAttrAssign-roundtrip-ATgtSignal-RavString
        ; parseRawAttrAssign-roundtrip-ATgtSignal-RavDecRatFrac
        ; parseRawAttrAssign-roundtrip-ATgtSignal-RavDecRatBareInt
        ; parseRawAttrAssign-roundtrip-ATgtEnvVar-RavString
        ; parseRawAttrAssign-roundtrip-ATgtEnvVar-RavDecRatFrac
        ; parseRawAttrAssign-roundtrip-ATgtEnvVar-RavDecRatBareInt
        ; parseRawAttrRel-roundtrip-ATgtNodeMsg-RavString
        ; parseRawAttrRel-roundtrip-ATgtNodeMsg-RavDecRatFrac
        ; parseRawAttrRel-roundtrip-ATgtNodeMsg-RavDecRatBareInt
        ; parseRawAttrRel-roundtrip-ATgtNodeSig-RavString
        ; parseRawAttrRel-roundtrip-ATgtNodeSig-RavDecRatFrac
        ; parseRawAttrRel-roundtrip-ATgtNodeSig-RavDecRatBareInt
        -- parseAttrLine 5-way `<|>` composer (3c.4) — 31 dispatchers
        -- across alt1 (RawDef-Rel × 2 scopes), alt2 (RawDefault × 3
        -- shapes), alt3 (RawDef-NotRel × 5 scopes), alt4 (RawAssign-Rel
        -- × 6), alt5 (RawAssign × 15).
        ; parseAttrLine-roundtrip-RawDef-Rel-NodeMsg
        ; parseAttrLine-roundtrip-RawDef-Rel-NodeSig
        ; parseAttrLine-roundtrip-RawDefault-RavString
        ; parseAttrLine-roundtrip-RawDefault-RavDecRatFrac
        ; parseAttrLine-roundtrip-RawDefault-RavDecRatBareInt
        ; parseAttrLine-roundtrip-RawDef-NotRel-Network
        ; parseAttrLine-roundtrip-RawDef-NotRel-Node
        ; parseAttrLine-roundtrip-RawDef-NotRel-Message
        ; parseAttrLine-roundtrip-RawDef-NotRel-Signal
        ; parseAttrLine-roundtrip-RawDef-NotRel-EnvVar
        ; parseAttrLine-roundtrip-RawAssign-ATgtNodeMsg-RavString
        ; parseAttrLine-roundtrip-RawAssign-ATgtNodeMsg-RavDecRatFrac
        ; parseAttrLine-roundtrip-RawAssign-ATgtNodeMsg-RavDecRatBareInt
        ; parseAttrLine-roundtrip-RawAssign-ATgtNodeSig-RavString
        ; parseAttrLine-roundtrip-RawAssign-ATgtNodeSig-RavDecRatFrac
        ; parseAttrLine-roundtrip-RawAssign-ATgtNodeSig-RavDecRatBareInt
        ; parseAttrLine-roundtrip-RawAssign-ATgtNetwork-RavString
        ; parseAttrLine-roundtrip-RawAssign-ATgtNetwork-RavDecRatFrac
        ; parseAttrLine-roundtrip-RawAssign-ATgtNetwork-RavDecRatBareInt
        ; parseAttrLine-roundtrip-RawAssign-ATgtNode-RavString
        ; parseAttrLine-roundtrip-RawAssign-ATgtNode-RavDecRatFrac
        ; parseAttrLine-roundtrip-RawAssign-ATgtNode-RavDecRatBareInt
        ; parseAttrLine-roundtrip-RawAssign-ATgtMessage-RavString
        ; parseAttrLine-roundtrip-RawAssign-ATgtMessage-RavDecRatFrac
        ; parseAttrLine-roundtrip-RawAssign-ATgtMessage-RavDecRatBareInt
        ; parseAttrLine-roundtrip-RawAssign-ATgtSignal-RavString
        ; parseAttrLine-roundtrip-RawAssign-ATgtSignal-RavDecRatFrac
        ; parseAttrLine-roundtrip-RawAssign-ATgtSignal-RavDecRatBareInt
        ; parseAttrLine-roundtrip-RawAssign-ATgtEnvVar-RavString
        ; parseAttrLine-roundtrip-RawAssign-ATgtEnvVar-RavDecRatFrac
        ; parseAttrLine-roundtrip-RawAssign-ATgtEnvVar-RavDecRatBareInt)
