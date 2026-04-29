{-# OPTIONS --safe --without-K #-}

-- Per-line-construct roundtrips for the DBC comment section (B.3.d Layer
-- 3 Commit 3b, migrated to Format DSL in 3d.5.d) — facade module.
--
-- Re-exports `parseComment-roundtrip` plus its scaffolding (`NameStop`,
-- `CommentTargetStop`, `buildCANId-rawCanIdℕ`) from
-- `Properties/Comments/Comment.agda`.  Mirrors the
-- `Properties/Topology.agda` and `Properties/Preamble.agda` pattern; the
-- per-construct submodule lives under `Properties/Comments/`.
--
-- Post-3d.5.d: `parseComment-roundtrip` is now a slim wrapper around the
-- universal Format DSL roundtrip applied to `commentFmt` (see
-- `Format/Comments.agda`).  Composition with the top-level Layer-4
-- aggregator is via the public `parseComment-roundtrip` symbol surfaced
-- here.
module Aletheia.DBC.TextParser.Properties.Comments where

open import Aletheia.DBC.TextParser.Properties.Comments.Comment public
  using (parseComment-roundtrip; NameStop; CommentTargetStop;
         buildCANId-rawCanIdℕ)
