{-# OPTIONS --without-K #-}

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
-- Tier A (byte-order / sign / keyword-dispatch scope tags, attr-type
-- STRING tag) + Tier B (string-literal escape body, mux marker with
-- embedded parseNatural).  `ATInt`/`ATFloat`/`ATHex`/`ATEnum` and
-- `SignalPresence` reclassified to Layer 3 (per-line-construct
-- payloads, not primitives — see `memory/project_b3d_universal_proof.md`).
open import Aletheia.DBC.TextParser.Properties.Primitives public
  using ( -- Probes + Identifier roundtrip
         parseIdentifier-roundtrip;
         mkIdentFromCharsUnsafe-on-valid;
         decompose-valid;
         satisfy-success-T;
         buildIdent-eq;
         -- Tier A primitives
         parseByteOrderDigit-roundtrip;
         parseSignFlag-roundtrip;
         parseOptionalStandardScope-ASNode-roundtrip;
         parseOptionalStandardScope-ASMessage-roundtrip;
         parseOptionalStandardScope-ASSignal-roundtrip;
         parseOptionalStandardScope-ASEnvVar-roundtrip;
         parseOptionalStandardScope-ASNetwork-roundtrip;
         parseRelScopeWS;
         parseRelScopeWS-ASNodeMsg-roundtrip;
         parseRelScopeWS-ASNodeSig-roundtrip;
         parseStringType-roundtrip;
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
