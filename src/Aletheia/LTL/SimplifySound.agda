{-# OPTIONS --safe --without-K #-}

-- Soundness of Rosu simplification (curated facade).
--
-- Purpose: Re-export `simplify-runL` and friends from per-layer submodules
--   so external consumers — chiefly `Adequacy/Pipeline.agda` — keep their
--   existing import path. The actual proofs live in two sibling modules so
--   that IDE jump-to-definition stays fast and each layer can be re-checked
--   independently:
--
--   SimplifySound.Decomposition — Sections 1-5: Boolean equality reflection
--                                  (≡ᵇ-proc-correct), And/Or idempotency,
--                                  nested idempotency, Always/Eventually
--                                  absorption on non-empty traces, and the
--                                  pointwise runL congruence helpers.
--                                  No `absorb`/`simplify` mention — pure
--                                  proof infrastructure about `finalizeL`
--                                  and `runL`.
--   SimplifySound.Composition   — Sections 6-8: `absorb-runL` (with Always/
--                                  Eventually absorption helpers),
--                                  `simplify-runL` (structural induction),
--                                  and the empty-trace corollary
--                                  `simplify-finalize-sv` used by the
--                                  pipeline adequacy proof.
--
-- Layering (proof firewall — each lower layer is quarantined):
--   * Decomposition reasons only about `finalizeL`/`stepL`/`runL` shapes.
--     No reference to `absorb` or `simplify`.
--   * Composition consumes only Decomposition's public API (≡ᵇ-proc-correct,
--     and-nested-idem-runL, or-nested-idem-runL, and-always-nonempty,
--     or-eventually-nonempty, runL-and-cong-r, runL-or-cong-r) and never
--     touches Decomposition's private decomposition helpers.
--
-- Public API (re-exported from both submodules):
--   Decomposition: ≡ᵇ-proc-correct; and-idem-runL; or-idem-runL;
--                  and-nested-idem-runL; or-nested-idem-runL;
--                  and-always-nonempty; or-eventually-nonempty;
--                  runL-and-right-True; runL-and-right-False;
--                  runL-and-cong-r; runL-or-right-True; runL-or-right-False;
--                  runL-or-cong-r
--   Composition:   absorb-runL; simplify-runL; simplify-finalize-sv
module Aletheia.LTL.SimplifySound where

-- ============================================================================
-- DECOMPOSITION LAYER: ≡ᵇ correctness, idempotency, runL congruence
-- ============================================================================
open import Aletheia.LTL.SimplifySound.Decomposition public
  using ( ≡ᵇ-proc-correct
        ; and-idem-runL
        ; or-idem-runL
        ; and-nested-idem-runL
        ; or-nested-idem-runL
        ; and-always-nonempty
        ; or-eventually-nonempty
        ; runL-and-right-True
        ; runL-and-right-False
        ; runL-and-cong-r
        ; runL-or-right-True
        ; runL-or-right-False
        ; runL-or-cong-r
        )

-- ============================================================================
-- COMPOSITION LAYER: absorb-runL, simplify-runL, simplify-finalize-sv
-- ============================================================================
open import Aletheia.LTL.SimplifySound.Composition public
  using ( absorb-runL
        ; simplify-runL
        ; simplify-finalize-sv
        )
