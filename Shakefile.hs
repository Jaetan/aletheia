-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
-- | The build: every rule group of shake/, registered in one Shake run.

import Development.Shake

import Rules.Library (libraryRules)
import Rules.Proofs (proofRules)
import Rules.Ffi (ffiRules)
import Rules.Gates (gateRules)
import Rules.Dist (distRules)
import Rules.Install (installRules)

main :: IO ()
main = shakeArgs shakeOptions{shakeFiles="build", shakeThreads=0, shakeChange=ChangeModtimeAndDigest} $ do
    -- The full offline CI sweep is invoked directly via `tools/run_ci.py`,
    -- NOT through a Shake `phony "ci"` target.
    --
    -- Reason: run_ci.py internally calls `cabal run shake -- build`,
    -- `cabal run shake -- check-properties`, etc.  If invoked through
    -- a Shake phony (parent: `cabal run shake -- ci`), the inner
    -- `cabal run` fails immediately because cabal-install's flock on
    -- `dist-newstyle/` is held by the outer process.
    --
    -- Two stable invocation paths:
    --   * Direct:    `python -m tools.run_ci`  (pre-push hook, manual runs)
    --   * Per-gate:  `cabal run shake -- check-properties` (etc.)

    libraryRules
    proofRules
    ffiRules
    gateRules
    distRules
    installRules
