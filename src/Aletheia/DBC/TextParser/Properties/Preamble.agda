-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Per-line-construct roundtrips for the DBC preamble — facade module.
--
-- Covers the three top-level preamble constructs:
--
--   * `parseVersion-roundtrip`    — `VERSION` line + trailing blank
--     lines.  First per-line construct; template-validates the
--     bind-chain composition pattern.
--   * `parseBitTiming-roundtrip`  — `BS_:` line with opaque tail,
--     canonical empty-body emission.
--   * `parseNamespace-roundtrip`  — `NS_ :` block with 25 canonical
--     keyword lines + trailing blank line.
--
-- Split into per-construct submodules under `Properties/Preamble/` to
-- keep each file near the ~500-line soft cap.  `Newline.agda` hosts
-- infrastructure reused across every subsequent per-line construct, not
-- just Preamble — kept here because that is where it first arose.
module Aletheia.DBC.TextParser.Properties.Preamble where

-- Newline infrastructure (reused by every per-line construct).
open import Aletheia.DBC.TextParser.Properties.Preamble.Newline public
  using (isNewlineStart;
         parseNewline-match-LF)

-- Per-construct roundtrips.
open import Aletheia.DBC.TextParser.Properties.Preamble.Version public
  using ()

open import Aletheia.DBC.TextParser.Properties.Preamble.BitTiming public
  using ()

open import Aletheia.DBC.TextParser.Properties.Preamble.Namespace public
  using ()

-- Load-bearing reduction canary for `Namespace.agda`'s `nsKeywords-valid`
-- discharge.  Imported (not re-exported) only to make the canary reachable
-- from the `check-properties` Shake walk; without an in-edge it would
-- silently bit-rot.
import Aletheia.DBC.TextParser.Properties.Preamble._Scratch
