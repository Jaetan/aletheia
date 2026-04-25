{-# OPTIONS --without-K #-}

-- Per-line-construct roundtrips for the DBC comment section (B.3.d Layer
-- 3 Commit 3b) — facade module.
--
-- Re-exports `parseComment-roundtrip` plus its scaffolding (`NameStop`,
-- `CommentTargetStop`, `buildCANId-rawCanIdℕ`) from
-- `Properties/Comments/Comment.agda`.  Mirrors the
-- `Properties/Topology.agda` and `Properties/Preamble.agda` pattern; the
-- per-construct submodule lives under `Properties/Comments/`.
--
-- The `parseComment-roundtrip` proof closes the most complex Layer-3
-- construct (5-way CommentTarget dispatch via `<|>`-chain plus the
-- string-lit / WS / `;` / newline tail), so the file is large (~2,500
-- lines).  Composition with the top-level Layer-4 aggregator is via the
-- public `parseComment-roundtrip` symbol surfaced here.
module Aletheia.DBC.TextParser.Properties.Comments where

open import Aletheia.DBC.TextParser.Properties.Comments.Comment public
  using (parseComment-roundtrip; NameStop; CommentTargetStop;
         buildCANId-rawCanIdℕ)
