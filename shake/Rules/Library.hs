-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- | The kernel library and what it is built from: the Agda toolchain
-- oracle, the MAlonzo output and its module list in aletheia.cabal, what
-- the C header feeds, the stand-in kernels and libaletheia-ffi.so itself.
module Rules.Library (libraryRules) where

import Development.Shake
import Development.Shake.Classes (Hashable, Binary, NFData)
import Development.Shake.FilePath
import System.Directory (getCurrentDirectory)
import qualified System.Directory as SysDir
import Data.List (isInfixOf, isPrefixOf, intercalate, sort)
import Data.Maybe (fromMaybe, listToMaybe)
import Data.Char (isDigit)
import Control.Monad (when, unless)
import Control.Exception (evaluate)
import GHC.Conc (getNumProcessors)
import Shared
import Rules.Ffi (checkFFINames)

-- | Shake oracle key for the Agda toolchain version.  The MAlonzo .hs (and thus
-- the .so) are a function of the agda BINARY version too, not only the .agda
-- sources — but the binary is not a file Shake can `need`, so it is tracked via an
-- oracle: `agda --version` is queried each build, and a change re-fires build-agda
-- and the .so rule.  (The stdlib pin + flags ARE a file, aletheia.agda-lib, so
-- those rules `need` it directly.)  Together these close the last untracked build
-- input, making the dependency graph fully honest.
newtype AgdaVersion = AgdaVersion ()
  deriving stock (Show, Eq)
  deriving newtype (Hashable, Binary, NFData)
type instance RuleResult AgdaVersion = String

-- | Convert a MAlonzo .hs path (relative to build/) to its Haskell module name,
-- e.g. "MAlonzo/Code/Aletheia/Protocol/ResponseFormat.hs"
--   ->  "MAlonzo.Code.Aletheia.Protocol.ResponseFormat".
malonzoModuleName :: FilePath -> String
malonzoModuleName = intercalate "." . splitDirectories . dropExtension

-- | Markers bounding the generated MAlonzo module list in aletheia.cabal's
-- foreign-library `other-modules`.  The list between them is the honest cabal-side
-- dependency graph: the .so is built from EVERY one of these .hs, so cabal must
-- track them (otherwise its up-to-date check skips GHC and ships a stale .so).
malonzoBeginMarker, malonzoEndMarker :: String
malonzoBeginMarker = "-- BEGIN GENERATED MALONZO MODULES (regenerate: cabal run shake -- gen-ffi-modules)"
malonzoEndMarker   = "-- END GENERATED MALONZO MODULES"

-- | Splice the generated MAlonzo module lines between the markers in the
-- aletheia.cabal text, preserving everything outside the region.  Idempotent:
-- the same module set yields identical output.  Returns the input UNCHANGED if
-- either marker is absent — in particular it never truncates the tail when the
-- END marker is missing (the caller, gen-ffi-modules, errors loudly in that case).
spliceMalonzoModules :: String -> [String] -> String
spliceMalonzoModules old modules =
    let ls = lines old
        (before, fromBegin) = break (isInfixOf malonzoBeginMarker) ls
    in case fromBegin of
        []                 -> old  -- BEGIN marker absent: leave untouched
        (beginLine : rest) ->
            case break (isInfixOf malonzoEndMarker) rest of
                (_, [])           -> old  -- END marker absent: refuse to truncate the tail
                (_, _ : afterEnd) ->
                    let indent   = takeWhile (== ' ') beginLine
                        modLines = map (indent ++) modules
                    in unlines (before ++ [beginLine] ++ modLines ++ [indent ++ malonzoEndMarker] ++ afterEnd)

-- | Memory-aware GHC job count for the FFI build.  Each `cabal build -jN` worker
-- is a GHC process that can reach the per-worker `-M3G` ceiling, so a naive
-- `-j <cores>` risks `cores × 3 GiB` and OOMs small CI runners (the old `-j16`
-- = up to 48 GiB).  Cap -j at BOTH the core count and available-RAM ÷ 3 GiB,
-- read at run time (never hardcoded — GHA runner specs drift).  Mirrors the
-- runtime detection in tools/_resources.py.
ffiBuildJobs :: IO Int
ffiBuildJobs = do
    cores <- getNumProcessors
    memAvailMB <- readMemAvailableMB
    let perWorkerMB = 3072  -- the -M3G per-worker ceiling
    pure $ max 1 (min cores (memAvailMB `div` perWorkerMB))

-- | Available system memory in MiB, parsed from /proc/meminfo's MemAvailable
-- line (reported in kB).  Returns a conservative 4096 MiB when the file or line
-- is absent (non-Linux / locked-down host) so the -j math degrades safely
-- rather than dividing by a stale-huge number.
readMemAvailableMB :: IO Int
readMemAvailableMB = do
    exists <- SysDir.doesFileExist "/proc/meminfo"
    if not exists
        then pure 4096
        else do
            contents <- readFile "/proc/meminfo"
            -- Accept only an all-digit token so `read` below cannot throw on an
            -- unexpected /proc/meminfo line; a non-numeric or absent value
            -- yields Nothing -> the 4096 MiB safe fallback (this function is
            -- meant to degrade gracefully on unusual hosts, never crash Shake).
            let kb = listToMaybe
                    [ kbStr
                    | line <- lines contents
                    , "MemAvailable:" `isPrefixOf` line
                    , kbStr <- take 1 (drop 1 (words line))
                    , not (null kbStr) && all isDigit kbStr
                    ]
            pure $ maybe 4096 ((`div` 1024) . read) kb

-- | Written by the rule that deletes what the C header feeds, and needed by the
-- library's rule, so the deletion happens before cabal runs.
shimHeaderStamp :: FilePath
shimHeaderStamp = "build/shim-header.stamp"

-- | The stand-in kernels the bindings' tests load in place of the library: one
-- at an ABI version no binding was written against, one exporting the version
-- alone, one exporting no kernel symbol, one whose kernel answers null, and
-- one that refuses the kernel's entries quoting what it was handed, answers a
-- known allocation count, and counts the closes and frees it is given.
-- Each is built from @haskell-shim/test/<name>.c@ against the kernel's header
-- into the directory the library is built in, where every binding's test looks
-- for it beside the library it stands in for.
standIns :: [FilePath]
standIns = map (\name -> "build/stand-ins" </> name <.> "so")
    ["stale_abi_kernel", "abi_only_kernel", "symbolless", "null_kernel", "recording_kernel"]

-- | The rules that build, list and clean the kernel library.
libraryRules :: Rules ()
libraryRules = do
    -- Toolchain-version oracle (see AgdaVersion): query `agda --version` once per
    -- build; a change re-fires build-agda + the .so rule (which `askOracle` it), so
    -- a toolchain bump rebuilds the MAlonzo output even with no .agda source change.
    _ <- addOracle $ \(AgdaVersion ()) -> do
        Stdout verOut <- cmd "agda" "--version"
        pure (strip verOut)

    phony "build" $ do
        need ["check-stdlib-version"]
        need ["build/libaletheia-ffi.so"]
        need standIns

    phony "build-agda" $ do
        need ["check-stdlib-version"]
        need ["build/MAlonzo/Code/Aletheia/Main.hs"]

    phony "build-haskell" $ do
        need ["check-stdlib-version"]
        need ["build/libaletheia-ffi.so"]

    phony "clean" $ do
        putInfo "Cleaning build artifacts..."
        removeFilesAfter "build" ["//*"]
        -- Agda writes its interfaces under `_build/<version>/agda/`, never
        -- beside the sources; a clean build re-derives them too.
        removeFilesAfter "_build" ["//*"]
        removeFilesAfter "haskell-shim" ["//MAlonzo"]
        cmd_ (Cwd "haskell-shim") "cabal clean"

    "build/MAlonzo/Code/Aletheia/Main.hs" %> \out -> do
        agdaSources <- getDirectoryFiles "src" ["//*.agda"]
        need (map ("src" </>) agdaSources)
        need ["aletheia.agda-lib"]       -- stdlib pin + flags (--erasure) are inputs too
        _ <- askOracle (AgdaVersion ())  -- agda binary version (not a `need`-able file)

        -- Shake's ChangeModtimeAndDigest tracks file content hashes
        -- When any .agda source changes, Shake detects it and re-runs this rule
        -- Agda will then update .agdai files as needed based on source changes
        putInfo "Compiling Agda to Haskell (this may take a few minutes)..."
        cores <- liftIO getNumProcessors
        cmd_ (Cwd "src")
            "agda"
            "+RTS" ("-N" ++ show cores) "-M16G" "-RTS"
            "--compile"
            "--compile-dir=../build"
            "--ghc-dont-call-ghc"
            "Aletheia/Main.agda"

        exists <- doesFileExist out
        if exists
            then do
                putInfo $ "MAlonzo output generated: " ++ out
                -- Check that FFI wrapper uses correct mangled names
                checkFFINames "haskell-shim/src/AletheiaFFI.hs"
            else error $ "Agda compilation failed: " ++ out ++ " not created"

    phony "gen-ffi-modules" $ do
        -- Regenerate the committed MAlonzo `other-modules` list in aletheia.cabal
        -- from the actual generated tree, so cabal's dependency graph for the
        -- foreign library is COMPLETE — it tracks every .hs the .so is built from.
        -- Without this, cabal's component up-to-date check never sees a MAlonzo
        -- change, skips GHC entirely, and ships a STALE .so.  The list is
        -- committed + reviewable; drift is caught at build time by
        -- `-Werror=missing-home-modules` (a module added but not listed) or
        -- cabal's "module not found" (a listed module removed).  Run this after
        -- adding/removing an Agda module, then commit aletheia.cabal.
        need ["build/MAlonzo/Code/Aletheia/Main.hs"]  -- ensure MAlonzo .hs exist
        -- Listed untracked, after the need: a tracked listing is one value per
        -- run, and a run whose compile adds a module would list the tree as it
        -- stood before the compile and leave that module out.
        malonzoFiles <- liftIO $ getDirectoryFilesIO "build" ["MAlonzo//**/*.hs"]
        let modules   = sort (map malonzoModuleName malonzoFiles)
            cabalPath = "haskell-shim/aletheia.cabal"
        old <- liftIO $ readFile cabalPath
        _   <- liftIO $ evaluate (length old)  -- force the lazy read before we write the same path
        unless (malonzoBeginMarker `isInfixOf` old) $
            error $ cabalPath ++ " is missing the marker\n  " ++ malonzoBeginMarker
                  ++ "\nAdd the BEGIN/END markers to the foreign-library other-modules first."
        unless (malonzoEndMarker `isInfixOf` old) $
            error $ cabalPath ++ " is missing the marker\n  " ++ malonzoEndMarker
                  ++ "\nBoth BEGIN and END markers are required; refusing to rewrite without END."
        let new = spliceMalonzoModules old modules
        if new == old
            then putInfo $ "FFI module list already in sync (" ++ show (length modules)
                         ++ " MAlonzo modules)."
            else do
                liftIO $ writeFile cabalPath new
                putInfo $ "Updated " ++ cabalPath ++ " ("
                        ++ show (length modules) ++ " MAlonzo modules listed)."

    -- What the C header feeds is rebuilt when the header changes.  cabal re-runs
    -- when `include/aletheia.h` changes, the .cabal listing it among its
    -- extra-source-files, but it recompiles a C source only when the .c file
    -- changed and re-runs hsc2hs only when the .hsc did: an edit to the header
    -- alone would link the old ABI version and the old structure layouts.  So
    -- when the header's content changes this rule deletes every output built
    -- from it, the objects of the shim's C sources and the modules hsc2hs
    -- writes, and cabal builds them again.  The stamp lists what was deleted.
    shimHeaderStamp %> \out -> do
        need ["haskell-shim/include/aletheia.h"]
        cSources <- getDirectoryFiles "haskell-shim" ["cbits/*.c", "test/*.c"]
        hscSources <- getDirectoryFiles "haskell-shim/src" ["//*.hsc"]
        let built = [takeFileName c -<.> ext | c <- cSources, ext <- ["o", "dyn_o"]]
                 ++ [h -<.> "hs" | h <- hscSources]
            tree = "haskell-shim/dist-newstyle"
        treeExists <- liftIO $ SysDir.doesDirectoryExist tree
        derived <- if treeExists
            then liftIO $ getDirectoryFilesIO tree (map ("//" ++) built)
            else pure []
        liftIO $ mapM_ (SysDir.removeFile . (tree </>)) derived
        writeFileChanged out (unlines derived)

    -- A stand-in kernel, compiled as C with the compiler CC names.
    "build/stand-ins/*.so" %> \out -> do
        let source = "haskell-shim/test" </> takeBaseName out <.> "c"
        headers <- getDirectoryFiles "" ["haskell-shim/include//*.h"]
        need (source : headers)
        cc <- fromMaybe "cc" <$> getEnv "CC"
        cmd_ cc ["-shared", "-fPIC", "-I", "haskell-shim/include", "-o", out, source]

    "build/libaletheia-ffi.so" %> \out -> do
        -- HONEST DEPENDENCY GRAPH.
        -- The .so's TRUE inputs are the Agda SOURCES (the MAlonzo .hs are a pure
        -- function of them), the FFI shim, and the cabal config — NOT the
        -- generated MAlonzo .hs.  `need`ing the generated .hs as inputs was the
        -- staleness trap: they have no producing rule, so Shake digested them as
        -- source files at the wrong moment (before build-agda regenerated them),
        -- and the rule could skip on a real change.  Depending on the .agda
        -- sources (genuine, digest-tracked source files) re-fires this rule iff a
        -- source's CONTENT changed (shakeChange = ChangeModtimeAndDigest).
        agdaSources <- getDirectoryFiles "src" ["//*.agda"]
        need (map ("src" </>) agdaSources)
        need ["aletheia.agda-lib"]       -- toolchain inputs (mirror build-agda) so a
        _ <- askOracle (AgdaVersion ())  -- stdlib/flag/agda-version bump re-fires the .so
        need [ shimHeaderStamp
             , "haskell-shim/src/AletheiaFFI.hs"
             , "haskell-shim/src/AletheiaFFI/Marshal.hs"
             , "haskell-shim/src/AletheiaFFI/BinaryOutput.hs"
             , "haskell-shim/src/AletheiaFFI/Wire.hsc"
             , "haskell-shim/include/aletheia.h"
             , "haskell-shim/cbits/abi_version.c"
             , "haskell-shim/cbits/allocation.c"
             , "haskell-shim/test/ConstructorTest.hs"
             , "haskell-shim/aletheia.cabal"
             ]
        -- Ordering edge: build-agda's declared output is Main.hs; needing it runs
        -- the agda compile (regenerating the affected MAlonzo .hs) when any .agda
        -- changed, BEFORE cabal reads them below.  This is NOT the re-fire trigger
        -- — editing a non-Main module leaves Main.hs's digest unchanged; the
        -- .agda-source deps above are what re-fire this rule.
        need ["build/MAlonzo/Code/Aletheia/Main.hs"]

        -- The symlink cabal resolves MAlonzo.* through, (re)created idempotently
        -- in-body — never a phony `need` (a phony is always dirty and would force
        -- this rule to re-fire every invocation, the old non-idempotency bug).
        ensureMalonzoSymlink

        -- Delegate the .hs -> .so edge to cabal/GHC's own incremental build.
        -- GHC's recompilation checker is content-hash aware (mi_src_hash + ABI
        -- fingerprints; mtime is only a pre-filter), so it recompiles exactly the
        -- modules whose .hs CONTENT changed and relinks.  NO `touch`, NO `rm -rf`
        -- — those forced a full ~280-module rebuild on every invocation, the
        -- single biggest CI/dev-loop cost.  Verified incremental + non-stale by
        -- tools/check_build_incremental.py (run_ci's "build" prereq).
        putInfo "Building FFI shared library (incremental; cabal owns .hs -> .so)..."
        -- UR-3.3: pass -ffile-prefix-map through to GHC's C compiler so any
        -- C-side debug info / __FILE__ embeddings strip the build-host path.
        -- Cannot use the bare `-fdebug-prefix-map` GHC flag here — that was
        -- only added to GHC in 9.10, and we pin GHC 9.8.4 (see the CI
        -- workflows' GHC_VERSION).
        --
        -- Same-host reproducibility was verified empirically WITHOUT this flag
        -- (two clean builds → bit-identical libaletheia-ffi.so),
        -- so the flag is defense-in-depth against future GHC C-side embeds /
        -- enabling debug info on a downstream rebuild.  C++ binding gets the
        -- equivalent flag in cpp/CMakeLists.txt.
        repoRoot <- liftIO getCurrentDirectory
        -- Memory-aware GHC job count.  Each `-jN` worker is a GHC process that
        -- can reach the per-worker `+RTS -M3G -RTS` ceiling (the tripwire —
        -- typical MAlonzo modules compile in 0.3-1 GB; 3G fails fast on
        -- pathological growth).  A naive `-j <cores>` would risk cores × 3 GB
        -- and OOM a small CI runner (the old fixed `-j16` = up to 48 GB), so
        -- `ffiBuildJobs` caps -j at BOTH the core count and available-RAM ÷ 3 GB,
        -- read at run time from /proc/meminfo + getNumProcessors — never
        -- hardcoded, mirroring tools/_resources.py (GHA runner specs drift).
        -- -A64M raises GHC's nursery from the 4 MB default for a slight
        -- throughput win.  Wrap the RTS value in `[String]` so Shake's `cmd_`
        -- does NOT whitespace-split it (otherwise `+RTS`, `-A64M`, `-M3G`,
        -- `-RTS` become separate argv entries and cabal rejects them).
        jobs <- liftIO ffiBuildJobs
        putInfo $ "GHC build parallelism: -j" ++ show jobs
               ++ " (cores × available-RAM÷3GB cap)"
        cmd_ (Cwd "haskell-shim") "cabal" "build" ("-j" ++ show jobs)
            ("--ghc-options=-optc-ffile-prefix-map=" ++ repoRoot ++ "=.")
            ["--ghc-options=+RTS -A64M -M3G -RTS"]
            "aletheia-ffi"

        -- Find and copy the built .so.  cabal keeps a SEPARATE dist-newstyle
        -- tree per package version (aletheia-<VER>/…), so a bare
        -- `find … | head -1` is non-deterministic when a stale tree from a prior
        -- version lingers (readdir order is unstable) — after a version bump it
        -- can silently copy the OLD version's .so (verified: it shipped a
        -- Jun-build .so under a bumped version).  Scope to the CURRENT package
        -- version's subtree (the stable, semantic boundary — NOT cabal's
        -- internal component layout) and FAIL LOUD on anything but exactly one
        -- match rather than guessing: the exactly-one check is the real guard,
        -- so no coupling to the `f/aletheia-ffi/…` path is needed (there is one
        -- libaletheia-ffi.so per version tree).  (`dist` additionally prunes
        -- stale trees up front; this rule is the always-on guard.)
        cabalContents <- liftIO $ readFile "haskell-shim/aletheia.cabal"
        let ver = parseCabalVersion cabalContents
        when (null ver) $
            error "Could not parse `version:` from haskell-shim/aletheia.cabal"
        Stdout rawSo <- cmd (Cwd "haskell-shim") Shell
            ( "find dist-newstyle -type f -path '*/aletheia-" ++ ver
              ++ "/*' -name 'libaletheia-ffi.so'" )
        case filter (not . null) (map strip (lines rawSo)) of
            [trimmedPath] -> do
                cmd_ (Cwd "haskell-shim") "cp" trimmedPath ("../" ++ out)
                putInfo $ "Shared library created: " ++ out
                                ++ " (from aletheia-" ++ ver ++ ")"
            [] -> error $ "No libaletheia-ffi.so under haskell-shim/dist-newstyle"
                        ++ " for the current version aletheia-" ++ ver
                        ++ " (did `cabal build aletheia-ffi` run?)."
            many -> error $ "Ambiguous libaletheia-ffi.so for aletheia-" ++ ver
                        ++ " — expected exactly one, found "
                        ++ show (length many) ++ ": " ++ intercalate ", " many
