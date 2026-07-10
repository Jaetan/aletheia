-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# OPTIONS --safe --without-K #-}

-- Per-line-construct roundtrips for the DBC comment section, migrated to
-- the Format DSL — facade module.
--
-- Re-exports `parseComment-roundtrip` plus its scaffolding (`NameStop`,
-- `CommentTargetStop`, `buildCANId-rawCanIdℕ`) from
-- `Properties/Comments/Comment.agda`.  Mirrors the
-- `Properties/Topology.agda` and `Properties/Preamble.agda` pattern; the
-- per-construct submodule lives under `Properties/Comments/`.
--
-- `parseComment-roundtrip` is now a slim wrapper around the
-- universal Format DSL roundtrip applied to `commentFmt` (see
-- `Format/Comments.agda`).  Composition with the top-level
-- aggregator is via the public `parseComment-roundtrip` symbol surfaced
-- here.
module Aletheia.DBC.TextParser.Properties.Comments where

open import Aletheia.DBC.TextParser.Properties.Comments.Comment public
  using (parseComment-roundtrip; NameStop; CommentTargetStop;
         buildCANId-rawCanIdℕ;
         parseComments-roundtrip)
