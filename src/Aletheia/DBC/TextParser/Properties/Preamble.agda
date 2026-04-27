{-# OPTIONS --safe --without-K #-}

-- Per-line-construct roundtrips for the DBC preamble (B.3.d Layer 3)
-- — facade module.
--
-- Covers the three top-level preamble constructs:
--
--   * `parseVersion-roundtrip`    — `VERSION` line + trailing blank
--     lines.  First Layer-3 construct; template-validates the
--     bind-chain composition pattern.
--   * `parseBitTiming-roundtrip`  — `BS_:` line with opaque tail,
--     canonical empty-body emission.
--   * `parseNamespace-roundtrip`  — `NS_ :` block with 25 canonical
--     keyword lines + trailing blank line (pending Commit 3a Part 2).
--
-- Split into per-construct submodules under `Properties/Preamble/` to
-- keep each file near the ~500-line soft cap (see
-- `feedback_properties_facade_split.md`).  `Newline.agda` hosts
-- infrastructure reused across every subsequent Layer-3 commit, not
-- just Preamble — kept here because it landed as part of Commit 3a.
module Aletheia.DBC.TextParser.Properties.Preamble where

-- Newline infrastructure (reused by every Layer-3 commit).
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline public
  using (isNewlineStart;
         parseNewline-match-LF;
         parseNewline-fail-on-stop;
         manyHelper-parseNewline-exhaust;
         manyHelper-one-iter;
         many-parseNewline-one-LF-stop)

-- Per-construct roundtrips.
open import Aletheia.DBC.TextParser.Properties.Preamble.Version public
  using (parseVersion-roundtrip)

open import Aletheia.DBC.TextParser.Properties.Preamble.BitTiming public
  using (parseBitTiming-roundtrip)

open import Aletheia.DBC.TextParser.Properties.Preamble.Namespace public
  using (parseNamespace-roundtrip; isNSLineStart)

-- Load-bearing reduction canary for `Namespace.agda`'s `nsKeywords-valid`
-- discharge.  Imported (not re-exported) only to make the canary reachable
-- from the `check-properties` Shake walk; without an in-edge it would
-- silently bit-rot — the failure mode warned about in
-- `feedback_check_properties_aggregator_walks.md`.
import Aletheia.DBC.TextParser.Properties.Preamble._Scratch
