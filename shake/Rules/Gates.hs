-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
-- | The gates that run a repository tool, and the stdlib pin every build
-- checks first.
module Rules.Gates (gateRules) where

import Development.Shake
import Development.Shake.FilePath
import System.Directory (getHomeDirectory)
import Data.List (stripPrefix)
import Control.Monad (when, unless, forM)
import Shared

-- | The stdlib pin and the tool-running gates.
gateRules :: Rules ()
gateRules = do
    phony "check-stdlib-version" $ do
        -- Verify that the globally installed agda-stdlib matches the
        -- version pinned in `aletheia.agda-lib`. Parses `depend:` from
        -- aletheia.agda-lib, then scans libraries listed in
        -- `$HOME/.agda/libraries` and reads each referenced `.agda-lib`
        -- for its `name:` field. Succeeds iff every required dep matches
        -- at least one installed library. Multi-line `depend:` blocks
        -- (indented continuation lines) are not supported — Aletheia
        -- currently depends only on standard-library on a single line.
        aletheiaLib <- liftIO $ readFile "aletheia.agda-lib"
        let requiredDeps =
              concat [ words rest
                     | l <- lines aletheiaLib
                     , Just rest <- [stripPrefix "depend:" l]
                     ]
        when (null requiredDeps) $
            error "aletheia.agda-lib: no `depend:` line or empty value"
        home <- liftIO getHomeDirectory
        let librariesFile = home </> ".agda" </> "libraries"
        libExists <- doesFileExist librariesFile
        unless libExists $
            error $ "check-stdlib-version failed: "
                 ++ librariesFile ++ " not found. "
                 ++ "Set up Agda libraries config "
                 ++ "(see docs/development/BUILDING.md)"
        libContent <- liftIO $ readFile librariesFile
        let expandHome p = case stripPrefix "~/" p of
                               Just rest -> home </> rest
                               Nothing   -> p
        let paths = [ expandHome s
                    | l <- lines libContent
                    , let s = strip l
                    , not (null s)
                    ]
        names <- forM paths $ \p -> do
            ex <- doesFileExist p
            if ex then do
                c <- liftIO $ readFile p
                let nm = case [ strip w
                              | l <- lines c
                              , Just rest <- [stripPrefix "name:" l]
                              , w <- take 1 (words rest)
                              ] of
                           (n:_) -> n
                           []    -> ""
                return (p, nm)
            else return (p, "")
        let missing =
              [ required
              | required <- requiredDeps
              , null [p | (p, nm) <- names, nm == required]
              ]
        unless (null missing) $ do
            let detail = unlines
                    [ "  " ++ p ++ ": "
                       ++ (if null nm then "<missing or unreadable>" else nm)
                    | (p, nm) <- names
                    ]
            error $ unlines
                [ ""
                , "════════════════════════════════════════════════════════════════"
                , "ERROR: stdlib version mismatch"
                , "════════════════════════════════════════════════════════════════"
                , ""
                , "  aletheia.agda-lib requires: " ++ unwords requiredDeps
                , "  Missing: " ++ unwords missing
                , "  Installed libraries from " ++ librariesFile ++ ":"
                , detail
                , "  Fix: install the missing dependency and register it in "
                , "  " ++ librariesFile
                , ""
                , "════════════════════════════════════════════════════════════════"
                , ""
                ]
        putInfo $ "Stdlib version OK: " ++ unwords requiredDeps

    phony "check-changelog" $ do
        -- Commit subjects and the CHANGELOG, by the rules tools/check_changelog.py's
        -- docstring lists; it is Python so local CI runs it without rebuilding
        -- the Shake binary.
        cmd_ pythonBin "-m" "tools.check_changelog"

    phony "check-gate-claim" $ do
        -- Gate-claim integrity enforcer: a commit may not assert that gates are
        -- clean unless a sweep observed the build sources it commits.  When a
        -- commit message contains a gate-clean assertion ("all gates clean",
        -- "gates green", etc.), the check digests the commit's build sources
        -- and asks for a sweep that recorded that digest: the sweep this
        -- target runs inside, which exports the digest of the tree it
        -- observes, or a passed log under tools/ci-output/ whose header
        -- carries it.  Content, never a timestamp: a checkout moves mtimes
        -- and no verdict.
        --
        -- Defaults to HEAD-mode when invoked via Shake (a named commit is the
        -- audit form, for a commit that is no longer HEAD).
        cmd_ pythonBin "-m" "tools.check_gate_claim" "HEAD"

    phony "check-haskell-ledger" $ do
        -- The building guide's Haskell ledger names the libraries the kernel
        -- library links: the ones the bundle carries, read as the dist rule
        -- reads them (getGhcDeps), and the system ones it does not.  The
        -- checker is Python, so the tables are read by the parser every
        -- documentation gate reads Markdown with.
        need ["build/libaletheia-ffi.so"]
        ghcDeps <- getGhcDeps "build/libaletheia-ffi.so"
        cmd_ pythonBin "-m" "tools.check_haskell_ledger" "build/libaletheia-ffi.so" ghcDeps

    phony "check-bundle-licences" $ do
        -- The tree keeps the licence texts of every library the dist rule
        -- bundles, the kernel library (with the Agda code compiled into it)
        -- and its GHC dependencies (getGhcDeps), recorded with their hashes,
        -- the upstream sources they were taken from and the GHC whose source tarball
        -- is one of them, so a GHC, Agda or Agda library bump fails here, on
        -- the change that makes it, not at a release.  The source audit's
        -- verdicts (packaging/licenses/audit.yaml) are held to the same
        -- record, so the bump also fails until its tarballs are scanned again.
        -- The dist rule needs this target before it stages the texts.
        need ["build/libaletheia-ffi.so"]
        ghcDeps <- getGhcDeps "build/libaletheia-ffi.so"
        cmd_ pythonBin "-m" "tools.bundle_licences" "check" ("build/libaletheia-ffi.so" : ghcDeps)

    phony "check-runbook" $ do
        -- Runbook coverage gate.  AGENTS.md cat 22 mandates
        -- that every structured log event the bindings emit has a matching
        -- entry in docs/operations/RUNBOOK.md.  This script parses
        -- docs/LOG_EVENTS.yaml and verifies every event name appears as a
        -- `#### `<name>`` heading in the runbook.  Missing entries fail the
        -- gate — operators must not be left blind on an event the code emits.
        cmd_ pythonBin "-m" "tools.check_runbook_coverage"

    phony "check-limits-parity" $ do
        -- Limits SSOT parity gate.  The Agda `Aletheia.Limits` module is the
        -- single source of truth for every adversarial-input bound (AGENTS.md
        -- universal rule).  The Go, Python and C++ bindings each mirror it,
        -- and each header claims the values are mirrored verbatim; this
        -- script enforces that promise on all three.  Failing on: a missing
        -- required mirror, a numeric value mismatch, a BoundKind wire-string
        -- mismatch, or either side holding an entry the other lacks.
        cmd_ pythonBin "-m" "tools.check_limits_parity"

    phony "check-stability-bench" $ do
        -- Stability-bench coverage gate.  AGENTS.md cat 16 /
        -- 25 / 26 / 27 mandate per-binding long-run leak detection harnesses
        -- (RSS, FD, threads/goroutines, malloc_info, StablePtr / ctypes /
        -- logger handlers).  This script parses docs/STABILITY_BENCH.yaml
        -- and verifies every (binding, sub_check) pair's source_marker is
        -- present in the named harness file — catches silent removal
        -- without running the harnesses.  The dynamic counterpart that
        -- actually runs the bench is `tools/stability_run.py`, gated
        -- behind ALETHEIA_STABILITY_CHECK=1 in `tools/run_ci.py`.
        cmd_ pythonBin "-m" "tools.check_stability_bench"

    phony "check-mutation-setup" $ do
        -- Mutation-setup coverage gate.  AGENTS.md cat 14(g)
        -- mandates per-binding mutation testing on hot-path modules.  This
        -- script holds docs/MUTATION_BENCH.yaml and each lane's
        -- configuration to the tree, the invariants its module docstring
        -- lists, without running the mutation tools (each binding's tool
        -- takes 30 min - 2 hours).
        -- Dynamic counterpart that actually runs mutmut / gremlins / Mull /
        -- cargo-mutants is `tools/mutation_run.py`, gated behind
        -- ALETHEIA_MUTATION_CHECK=1 (or `--mutation`) in `tools/run_ci.py`.
        cmd_ pythonBin "-m" "tools.check_mutation_setup"

    phony "check-wire-code-emitters" $ do
        -- Every wire code names a constructor the runtime builds: each
        -- formatter arm (`parseErrorCode`, `boundKindCode`, the u8 reason
        -- codes, …) is read from the Agda source, and its constructor must
        -- appear applied, not only matched, in the generated Haskell of the
        -- runtime closure.  A constructor nothing builds is a code no response
        -- can carry, which every binding still mirrors.
        need ["build/MAlonzo/Code/Aletheia/Main.hs", "haskell-shim/runtime-closure.snapshot"]
        cmd_ pythonBin "-m" "tools.check_wire_code_emitters"
