-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
import Development.Shake
import Development.Shake.Classes (Hashable, Binary, NFData)
import Development.Shake.FilePath
import System.Directory (createDirectoryLink, removePathForcibly,
                         getHomeDirectory, createDirectoryIfMissing,
                         removeDirectoryRecursive,
                         getCurrentDirectory)
import qualified System.Directory as SysDir
import System.Info (os)
import System.Environment (lookupEnv)
import System.Exit (ExitCode(..))
import System.IO.Error (catchIOError)
import Data.List (isInfixOf, isPrefixOf, stripPrefix, nub, intercalate, sort)
import Data.Maybe (listToMaybe)
import Data.Char (isSpace, isDigit)
import Control.Monad (when, unless, forM, forM_)
import Control.Exception (evaluate)
import GHC.Conc (getNumProcessors)

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

-- | Trim whitespace from both ends of a string
strip :: String -> String
strip = dropWhile isSpace . reverse . dropWhile isSpace . reverse

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

-- | Ensure the `haskell-shim/MAlonzo -> ../build/MAlonzo` symlink exists.  cabal
-- resolves the generated `MAlonzo.*` modules through it (`hs-source-dirs: src, .`
-- in aletheia.cabal), since MAlonzo output lives outside the package subtree.
--
-- Idempotent and content-neutral: it (re)creates the link ONLY when missing, so
-- it never perturbs cabal's incremental state.  This replaces the former phony
-- `create-symlink` rule — a phony is always dirty, so `need`ing it forced the
-- .so rule to re-fire (and thus full-rebuild) on every invocation.  Creating the
-- link in-body instead means it is touched only when the .so is genuinely being
-- (re)built.  The symlink's own mtime is irrelevant to GHC: it stats through the
-- link to the real `build/MAlonzo/**/*.hs` files, whose mtimes are unchanged.
ensureMalonzoSymlink :: Action ()
ensureMalonzoSymlink = do
    let symlinkPath = "haskell-shim/MAlonzo"
        target      = "../build/MAlonzo"
    -- `pathIsSymbolicLink` throws if the path is absent; treat that as "no link".
    isLink <- liftIO $ SysDir.pathIsSymbolicLink symlinkPath
                         `catchIOError` \_ -> pure False
    unless isLink $ do
        putInfo $ "Creating symlink: " ++ symlinkPath ++ " -> " ++ target
        liftIO $ removePathForcibly symlinkPath  -- clear a stale non-symlink, if any
        if os == "mingw32"
            then cmd_ "cmd" "/c" "mklink /D" symlinkPath target
            else liftIO $ createDirectoryLink target symlinkPath

-- | Extract the mangled MAlonzo name for a given Agda function from generated Haskell.
-- Looks for pattern: "d_<funcName>_XX ::"
extractMangledName :: String -> String -> Maybe String
extractMangledName funcName content =
    let prefix = "d_" ++ funcName ++ "_"
    in listToMaybe [name | line <- lines content,
                           funcName `isInfixOf` line,
                           "::" `isInfixOf` line,
                           let name = takeWhile (/= ' ') (dropWhile (== ' ') line),
                           prefix `isInfixOf` name]

-- | Extract the function name currently used in the FFI wrapper for a given Agda function.
-- Looks for pattern: "<qualifier>.d_<funcName>_XX" where qualifier is e.g. "AgdaJSON" or "AgdaBin".
extractFFIName :: String -> String -> String -> Maybe String
extractFFIName qualifier funcName content =
    let prefix = "d_" ++ funcName ++ "_"
        qualPrefix = qualifier ++ "." ++ prefix
        qualLen = length qualifier + 1 -- qualifier + "."
    in listToMaybe [cleaned | line <- lines content,
                              qualifier `isInfixOf` line,
                              funcName `isInfixOf` line,
                              let parts = words line,
                              name <- parts,
                              qualPrefix `isInfixOf` name,
                              let cleaned = drop qualLen name,
                              prefix `isInfixOf` cleaned]

-- | Check that the FFI wrapper uses the correct mangled name for a single function.
checkOneFFIName :: String -> String -> String -> String -> Action ()
checkOneFFIName qualifier funcName malonzoContent ffiContent =
    case (extractMangledName funcName malonzoContent, extractFFIName qualifier funcName ffiContent) of
        (Just generatedName, Just ffiName) ->
            when (generatedName /= ffiName) $ do
                putError $ unlines
                    [ ""
                    , "════════════════════════════════════════════════════════════════"
                    , "ERROR: MAlonzo function name mismatch for " ++ funcName ++ "!"
                    , "════════════════════════════════════════════════════════════════"
                    , ""
                    , "  Generated by Agda:  " ++ generatedName
                    , "  Currently in FFI:   " ++ ffiName
                    , ""
                    , "The Agda code structure changed, causing MAlonzo to generate"
                    , "a different mangled name. Update the FFI wrapper to match."
                    , ""
                    , "To fix, run:"
                    , "  sed -i 's/" ++ ffiName ++ "/" ++ generatedName ++ "/g' haskell-shim/src/AletheiaFFI.hs"
                    , ""
                    , "Then rebuild:"
                    , "  cabal run shake -- build"
                    , ""
                    , "════════════════════════════════════════════════════════════════"
                    , ""
                    ]
                error $ "FFI name mismatch for " ++ funcName ++ " - see above for fix instructions"
        (Nothing, _) ->
            putWarn $ "Could not extract mangled name for " ++ funcName ++ " from MAlonzo output"
        (_, Nothing) ->
            putWarn $ "Could not extract " ++ funcName ++ " name from FFI wrapper"

-- | FFI export specification. Single source of truth for both
-- `checkFFINames` (verifies AletheiaFFI.hs matches MAlonzo output) and
-- the `check-ffi-exports`/`regen-ffi-exports` phonies (maintain a
-- checked-in snapshot of mangled names to catch silent drift).
data FFIExport = FFIExport
    { ffiQualifier :: String  -- ^ qualifier used in AletheiaFFI.hs ("AgdaJSON", "AgdaBin", "AgdaState")
    , ffiFuncName  :: String  -- ^ function name as written in Agda
    , ffiModule    :: String  -- ^ MAlonzo output path relative to `build/MAlonzo/Code/`, no .hs suffix
    }

-- | Every FFI-exported Agda definition that the Haskell shim calls.
-- Keep ordered so the regenerated snapshot has a stable diff.
ffiExports :: [FFIExport]
ffiExports =
    [ FFIExport "AgdaJSON"  "processJSONLine"          "Aletheia/Main/JSON"
    , FFIExport "AgdaBin"   "processFrameDirect"       "Aletheia/Main/Binary"
    , FFIExport "AgdaBin"   "processEventDirect"       "Aletheia/Main/Binary"
    , FFIExport "AgdaBin"   "processStartStreamDirect" "Aletheia/Main/Binary"
    , FFIExport "AgdaBin"   "processEndStreamDirect"   "Aletheia/Main/Binary"
    , FFIExport "AgdaBin"   "processFormatDBCDirect"   "Aletheia/Main/Binary"
    , FFIExport "AgdaBin"   "processExtractDirect"     "Aletheia/Main/Binary"
    , FFIExport "AgdaBin"   "processBuildFrameBin"     "Aletheia/Main/Binary"
    , FFIExport "AgdaBin"   "processUpdateFrameBin"    "Aletheia/Main/Binary"
    , FFIExport "AgdaBin"   "processExtractBin"        "Aletheia/Main/Binary"
    , FFIExport "AgdaState" "initialState"             "Aletheia/Protocol/StreamState/Types"
    , FFIExport "AgdaRR"    "formatRational"           "Aletheia/DBC/RationalRenderer"
    ]

-- | Load the MAlonzo module contents needed by `ffiExports`, deduplicating
-- across entries that share a module.
loadFFIModuleContents :: Action [(String, String)]
loadFFIModuleContents = do
    let modules = nub (map ffiModule ffiExports)
    liftIO $ forM modules $ \m -> do
        c <- readFile ("build/MAlonzo/Code" </> m <.> "hs")
        return (m, c)

-- | Human-readable label for FFI snapshot entry kinds (`F`/`C`/`T`).
-- Used in `check-ffi-exports` diagnostics — keeps the error message
-- self-explanatory ("function snapshot drift" vs "constructor …").
kindLabel :: String -> String
kindLabel "F" = "function"
kindLabel "C" = "constructor"
kindLabel "T" = "type"
kindLabel k   = "entry (" ++ k ++ ")"

-- | Reverse of MAlonzo's name mangling for entries in the FFI snapshot:
-- strips the "d_" prefix and trailing "_<digits>" suffix. Assumes
-- function names are alphanumeric (no underscores) — true for every
-- entry in `ffiExports`.
inferFuncName :: String -> String
inferFuncName mangled =
    case stripPrefix "d_" mangled of
        Just rest -> reverse (drop 1 (dropWhile isDigit (reverse rest)))
        Nothing   -> mangled

-- | Check that the FFI wrapper uses the correct mangled names for all
-- exported functions listed in `ffiExports`.
checkFFINames :: FilePath -> Action ()
checkFFINames ffiFile = do
    ffiContent <- liftIO $ readFile ffiFile
    moduleContents <- loadFFIModuleContents
    forM_ ffiExports $ \e ->
        case lookup (ffiModule e) moduleContents of
            Just c  -> checkOneFFIName (ffiQualifier e) (ffiFuncName e) c ffiContent
            Nothing -> return ()  -- unreachable: loadFFIModuleContents covers every module

-- | Parse the digest-pinned base image from Dockerfile.runtime.
-- Returns the value after `FROM ` up to end-of-line (e.g.
-- `python:3.14-slim@sha256:...`).  Falls back to "unknown" if no
-- `FROM` line is found.
parseFromBase :: String -> String
parseFromBase dockerfile =
    case [ rest | l <- lines dockerfile
                , Just rest <- [stripPrefix "FROM " l]
                ]
      of (x:_) -> strip x
         []    -> "unknown"

-- | Parse the pinned libgmp10 version from Dockerfile.runtime.
-- Looks for the `libgmp10=<version>` token inside an `apt-get install`
-- line and returns just the version.  Falls back to "unknown".
parseLibgmpVersion :: String -> String
parseLibgmpVersion dockerfile =
    case [ ver | tok <- words dockerfile
               , Just rest <- [stripPrefix "libgmp10=" tok]
               , let ver = takeWhile (\c -> c /= ' ' && c /= '\\' && c /= '\n') rest
               , not (null ver)
               ]
      of (x:_) -> x
         []    -> "unknown"

-- | Get GHC runtime .so dependencies for a shared library.
-- Runs ldd and filters for libraries under GHC's lib directory.
getGhcDeps :: FilePath -> Action [FilePath]
getGhcDeps soPath = do
    Stdout ghcLibDir <- cmd "ghc" "--print-libdir"
    let ghcBase = strip ghcLibDir
    Stdout lddOutput <- cmd "ldd" soPath
    let deps = [ resolvedPath
               | line <- lines lddOutput
               , let ws = words line
               , length ws >= 3
               , ws !! 1 == "=>"
               , let resolvedPath = ws !! 2
               , ghcBase `isPrefixOf` resolvedPath
               ]
    return deps

-- | Compute SHA-256 of a file via the system sha256sum binary.
-- Returns the hex digest only (no path/whitespace).
sha256file :: FilePath -> Action String
sha256file p = do
    Stdout out <- cmd "sha256sum" p
    return $ takeWhile (/= ' ') out

-- | Check that patchelf and Python 3.12+ are available.
checkPrerequisites :: Action ()
checkPrerequisites = do
    Exit patchelfCode <- cmd Shell "command -v patchelf >/dev/null 2>&1"
    case patchelfCode of
        ExitSuccess -> return ()
        ExitFailure _ -> error $ unlines
            [ "patchelf is required for install but not found."
            , "Install it with:"
            , "  Ubuntu/Debian: sudo apt install patchelf"
            , "  macOS:         brew install patchelf"
            , "  Fedora:        sudo dnf install patchelf"
            ]
    Exit pyCode <- cmd Shell (bootstrapPython ++ " -c 'import sys; sys.exit(0 if sys.version_info >= (3,14) else 1)'")
    case pyCode of
        ExitSuccess -> return ()
        ExitFailure _ -> error (bootstrapPython ++ " (Python 3.14+) is required; ensure python3.14 is on PATH.")

-- | Proof-only modules — the SINGLE SOURCE for `check-properties`, type-checked
-- in one warm `agda --interaction-json` process (tools.warm_check_properties).
-- Each is unreachable from Main.agda's runtime closure, so the main
-- build walk does not cover it; each is an explicit walk root, and dropping one
-- silently stops type-checking its subtree (B.3.d Commit 4/6 shipped a latent
-- `RawSignal : ℚ`-vs-DecRat mismatch in TextParser/Topology precisely because a
-- root was missing).  Rationale per `feedback_check_properties_aggregator_walks`;
-- per-module history is in this file's git log (pre-refactor inline comments).
-- | Interpreters for build tooling.  The project requires Python 3.14 (PEP 758
-- `except A, B` syntax lives in tools/, plus requires-python>=3.14), so bare
-- `python3` -- often still 3.12/3.13 -- would `SyntaxError` on the 3.14-only
-- tools.  Build-tooling invocations therefore run in the dev venv
-- (`python/.venv`), which is 3.14 AND carries the project's runtime deps: some
-- meta-checks `import yaml` (PyYAML), absent from a bare interpreter (cf.
-- feedback_use_venv_for_gates).  Shake runs with cwd = repo root, so the
-- relative venv path resolves.  `bootstrapPython` is the system 3.14 used only
-- to create venvs and as the version-gate target.
pythonBin :: String
pythonBin = "python/.venv/bin/python3"

bootstrapPython :: String
bootstrapPython = "python3.14"

proofModules :: [String]
proofModules =
    -- Parser / top-level JSON
    [ "Aletheia/Parser/Properties.agda"
    , "Aletheia/JSON/Properties.agda"
    -- Protocol
    , "Aletheia/Protocol/JSON/Properties.agda"
    , "Aletheia/Protocol/ResponseFormat/Properties.agda"
    , "Aletheia/Protocol/FrameProcessor/Properties.agda"
    , "Aletheia/Protocol/Handlers/Properties.agda"
    , "Aletheia/Protocol/Adequacy/WarmCache.agda"
    -- CAN
    , "Aletheia/CAN/Encoding/Properties.agda"
    , "Aletheia/CAN/Batch/Properties.agda"
    , "Aletheia/CAN/DLC/Properties.agda"
    , "Aletheia/CAN/SignalExtraction/Properties.agda"
    , "Aletheia/CAN/Endianness/Properties.agda"
    -- DBC
    , "Aletheia/DBC/Properties.agda"
    , "Aletheia/DBC/JSONParser/Properties.agda"
    , "Aletheia/DBC/Validity/Theorem.agda"
    , "Aletheia/DBC/Formatter/Properties.agda"
    , "Aletheia/DBC/Formatter/Bounded.agda"
    , "Aletheia/DBC/TextParser/Properties.agda"
    , "Aletheia/DBC/TextParser/DecRatParse/Properties.agda"
    -- RationalRenderer itself IS reached from Main (FFI shim); .Properties is not.
    , "Aletheia/DBC/RationalRenderer/Properties.agda"
    , "Aletheia/DBC/RationalRenderer/Faithful.agda"
    -- TextParser / TextFormatter aggregators: not proofs, but pulling them in
    -- forces the full submodule tree to type-check (unreachable from Main).
    , "Aletheia/DBC/TextParser.agda"
    , "Aletheia/DBC/TextFormatter.agda"
    , "Aletheia/DBC/DecRat/RationalRoundtrip.agda"
    , "Aletheia/DBC/DecRat/RationalSoundness.agda"
    -- WellFormedText / ValueDescResolves / Format DSL: walk roots currently
    -- unimported by downstream proofs; explicit roots keep them from bit-rotting.
    , "Aletheia/DBC/Formatter/WellFormedText.agda"
    , "Aletheia/DBC/Formatter/WellFormedText/ValueDescResolves.agda"
    -- E.2 bounded slice: derives the five per-section name-stop fields of
    -- WellFormedTextDBCAgg from Identifier-validity (DEFERRED_ITEMS.md E.2).
    -- Unimported — the FFI-boundary consumer is deferred along with the two
    -- heavy fields (MessageWF / WFAttribute) — so an explicit root keeps it
    -- from bit-rotting.
    , "Aletheia/DBC/TextParser/Properties/WellFormedFromValidity.agda"
    -- A.2 BO_TX_BU_ inverse-bridge: `attachSenders (collectSenders msgs) msgs
    -- ≡ msgs` under msg-id uniqueness (DEFERRED_ITEMS.md A.2).  Unimported
    -- until the formatter/parser integration lands the senders section on the
    -- text wire — explicit root keeps the base bridge from bit-rotting.
    , "Aletheia/DBC/TextParser/Properties/Aggregator/Refine/Senders.agda"
    -- A.2 composition: nests the senders bridge with the VAL_ value-desc
    -- bridge over `clearBothMsg` parse output — the form `buildDBC` presents
    -- once the senders section is wired.  Also unimported until integration;
    -- explicit root keeps the composition green in the interim.
    , "Aletheia/DBC/TextParser/Properties/Aggregator/Refine/SendersCompose.agda"
    , "Aletheia/DBC/TextParser/Format.agda"
    , "Aletheia/DBC/TextParser/Format/RegressionTests.agda"
    , "Aletheia/DBC/TextParser/Format/ValueTable.agda"
    , "Aletheia/DBC/CanonicalReceivers.agda"
    , "Aletheia/DBC/TextParser/Format/Receivers.agda"
    , "Aletheia/DBC/TextParser/Format/Receivers/Roundtrip.agda"
    -- A.2 BO_TX_BU_ line Format DSL + roundtrip (mirrors ValueDescription).
    -- Unimported until the parser/formatter integration; explicit root keeps
    -- the DSL roundtrip green in the interim.
    , "Aletheia/DBC/TextParser/Format/MessageSenders.agda"
    -- A.2 BO_TX_BU_ dispatcher slim + section stops + emit bridge (mirrors
    -- Dispatcher.Simple.ValueDesc).  Transitively covers the formatter emitter
    -- (TextFormatter.MessageSenders).  Unimported until the atomic integration
    -- wires the TBO dispatch arm; explicit root keeps it green meanwhile.
    , "Aletheia/DBC/TextParser/Properties/Aggregator/Dispatcher/Simple/MsgSenders.agda"
    , "Aletheia/DBC/TextParser/Format/SignalLine.agda"
    , "Aletheia/DBC/TextParser/Format/SignalLine/Roundtrip.agda"
    , "Aletheia/DBC/TextParser/Format/Nodes.agda"
    , "Aletheia/DBC/TextParser/Format/Preamble.agda"
    -- This ONE root (Substrate/Unsafe, the sole non-`--safe` module) transitively
    -- covers the entire Aggregator/Universal subtree (Dispatcher / ManyTopStmts /
    -- Partition / Refine / BodyBridge / Foundations) — see the feedback file.
    , "Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda"
    -- LTL
    , "Aletheia/LTL/JSON/Properties.agda"
    , "Aletheia/LTL/Adequacy.agda"
    , "Aletheia/LTL/Adequacy/Pipeline.agda"
    , "Aletheia/LTL/Coalgebra/Properties.agda"
    , "Aletheia/LTL/Semantics/MTL.agda"
    , "Aletheia/LTL/Semantics/Duality.agda"
    , "Aletheia/LTL/TruthVal/Properties.agda"
    , "Aletheia/LTL/SignalPredicate/Cache/Properties.agda"
    , "Aletheia/LTL/SignalPredicate/Evaluation/Properties.agda"
    ]

main :: IO ()
main = shakeArgs shakeOptions{shakeFiles="build", shakeThreads=0, shakeChange=ChangeModtimeAndDigest} $ do

    -- Toolchain-version oracle (see AgdaVersion): query `agda --version` once per
    -- build; a change re-fires build-agda + the .so rule (which `askOracle` it), so
    -- a toolchain bump rebuilds the MAlonzo output even with no .agda source change.
    _ <- addOracle $ \(AgdaVersion ()) -> do
        Stdout verOut <- cmd "agda" "--version"
        pure (strip verOut)

    phony "build" $ do
        need ["check-stdlib-version"]
        need ["build/libaletheia-ffi.so"]

    phony "build-agda" $ do
        need ["check-stdlib-version"]
        need ["build/MAlonzo/Code/Aletheia/Main.hs"]

    phony "build-haskell" $ do
        need ["check-stdlib-version"]
        need ["build/libaletheia-ffi.so"]

    phony "check-properties" $ do
        -- Type-check every proof-only module in ONE warm `agda --interaction-json`
        -- process (stdlib + shared deps load once) instead of one `agda Module.agda`
        -- subprocess per module.  Catches proof-obligation failures (Status
        -- checked:false) and writes `.agdai` so the downstream build reuses the
        -- interfaces.  Replaces the former cold batch (one agda process per module,
        -- ~13× slower: 629s -> ~48s); same `proofModules` single source of truth.
        putInfo "Type-checking proof-only modules (one warm agda process)..."
        cmd_ pythonBin ("-m" : "tools.warm_check_properties" : proofModules)

    -- `iwyu` — regenerate the relevant .agdai and run the import analysis WITHOUT a
    -- full .hs/.so rebuild.  The .agda → .agdai (type-check) route is distinct from
    -- the .agda → .hs (compile) route the .so rule tracks; iwyu consumes .agdai
    -- only, so this does NOT depend on `build`.  The .agdai are regenerated
    -- incrementally by Agda's OWN interface cache — tools.iwyu's warm process
    -- re-checks each scoped module and Agda reuses unchanged interfaces, so only
    -- what actually changed is recomputed (no Shake-side .agdai tracking needed).
    -- A plain phony, like the other check-* gates: it always runs the analysis (a
    -- check should run, not be skipped behind a result-cache stamp — which would
    -- also miss changes to the iwyu tool itself).  Whole-tree (`--all`); for the
    -- branch-diff scope run `tools.iwyu --check --diff`.  `cabal run shake -- iwyu`.
    phony "iwyu" $ do
        need ["check-stdlib-version"]
        putInfo "Regenerating .agdai (Agda interface cache) + running IWYU..."
        cmd_ pythonBin "-m" "tools.iwyu" "--check" "--all"

    phony "check-invariants" $ do
        -- Enforce "postulates and Unsafe modules are limited to the
        -- allowlisted B.3.d substrate" project-wide.
        --
        -- Allowlist policy: exactly one Unsafe module is permitted —
        -- `Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda`,
        -- which carries the two `String ↔ List Char` bridging axioms
        -- (`toList∘fromList`, `fromList∘toList`) needed to compose the
        -- B.3.d universal roundtrip theorem.  These mirror stdlib's
        -- `Data.String.Unsafe` (proven by `trustMe` under `--with-K`),
        -- which is structurally unprovable in `--safe --without-K`.
        -- Any other `Unsafe`-named module OR any other `^postulate`
        -- line is rejected — adding one requires a paired Shakefile
        -- update and explicit user approval (see
        -- `feedback_no_suppression_without_approval.md`).
        --
        -- The grep below uses -l (filenames only) so we can compare
        -- paths against the allowlist; -r recurses; --include limits
        -- to .agda; -E enables the regex.  grep exits 1 when there
        -- are no matches, so we take Exit + Stdout explicitly and
        -- ignore the exit code.
        let allowedUnsafe =
                ["Aletheia/DBC/TextParser/Properties/Substrate/Unsafe.agda"]
        (Exit _, Stdout postulateOut) <-
            cmd "grep" "-rln" "--include=*.agda" "-E" "^postulate" "src/"
        let postulateFiles = lines (postulateOut :: String)
            stripSrc f = case stripPrefix "src/" f of
                           Just rest -> rest
                           Nothing   -> f
            unauthorisedPostulate =
                filter (\f -> stripSrc f `notElem` allowedUnsafe) postulateFiles
        unless (null unauthorisedPostulate) $ do
            putError $ "^postulate found in non-allowlisted Agda source:\n"
                    ++ unlines unauthorisedPostulate
            error "check-invariants failed"
        -- Two glob forms: "//*.Unsafe.agda" matches dotted suffixes
        -- (e.g. `Foo.Unsafe.agda`); "//Unsafe.agda" matches leaf
        -- `Unsafe.agda` files (the stdlib-style layout used by the
        -- substrate module).  Union of matches is the candidate set.
        unsafeMatches <-
            getDirectoryFiles "src" ["//*.Unsafe.agda", "//Unsafe.agda"]
        let unauthorisedUnsafe =
                filter (`notElem` allowedUnsafe) unsafeMatches
        unless (null unauthorisedUnsafe) $ do
            putError $ "Unauthorised Unsafe-named module(s) found: "
                    ++ show unauthorisedUnsafe
            error "check-invariants failed"
        putInfo $ "Invariants OK: postulates and Unsafe modules limited "
               ++ "to the allowlisted B.3.d substrate."

    phony "check-no-properties-in-runtime" $ do
        -- Runtime modules must not import Properties modules; a Properties
        -- import would transitively pull every lemma into MAlonzo output.
        let runtime = [ "src/Aletheia/Main.agda"
                      , "src/Aletheia/Main/JSON.agda"
                      , "src/Aletheia/Main/Binary.agda"
                      , "src/Aletheia/Protocol/Handlers.agda"
                      ]
        -- Wrap the regex in a singleton list so Shake's `cmd` does not split
        -- it on whitespace (the pattern contains a space between "open" and
        -- "import" and would otherwise become multiple argv entries).
        let pat = ["^open import .*\\.Properties\\b|^import .*\\.Properties\\b"]
        (Exit _, Stdout violations) <-
            cmd "grep" ["-nE"] pat runtime
        unless (null (violations :: String)) $ do
            putError $ "Runtime module imports a Properties module:\n" ++ violations
            error "check-no-properties-in-runtime failed"
        putInfo "No Properties imports in runtime modules."

    phony "count-modules" $ do
        agdaFiles <- getDirectoryFiles "src" ["//*.agda"]
        let n = length agdaFiles
        putInfo $ "Agda modules under src/: " ++ show n

    phony "check-fidelity" $ do
        -- MAlonzo constructor-drift smoke test.
        -- The cabal test-suite constructor-fidelity exercises the binary FFI
        -- path end-to-end with hand-rolled constructor calls; if a MAlonzo
        -- mangled name or constructor arity drifts relative to the shim, the
        -- test fails to compile OR segfaults on first frame.
        need ["build/libaletheia-ffi.so"]
        -- The .so rule creates the haskell-shim/MAlonzo symlink in-body, but it
        -- NO-OPS when the .so is already up to date — e.g. a warm build-tree cache
        -- restored on a fresh CI checkout, where the gitignored symlink is absent.
        -- cabal resolves the MAlonzo.* modules ConstructorTest imports through that
        -- symlink, so ensure it here too: idempotent, and independent of whether
        -- the .so rule fired this run.  (Without this, `cabal test` fails with
        -- "Could not find module MAlonzo.Code.…" — reproducible by removing the
        -- symlink against an up-to-date .so.)
        ensureMalonzoSymlink
        putInfo "Running MAlonzo constructor-fidelity test..."
        cmd_ (Cwd "haskell-shim") "cabal" "test" "constructor-fidelity"
             "--test-show-details=direct"

    phony "check-erasure" $ do
        -- Guard the FFI marshaling assumptions about MAlonzo output shape.
        -- After R18 cluster 17 (AGDA-B-22.1), CANId proof fields are
        -- `.(…)`-irrelevant — MAlonzo erases the cell entirely, so the
        -- constructors compile to single-Integer shape (no `AgdaAny`
        -- proof slot). Marshal.hs `mkAgdaCanId` constructs without the
        -- second arg. Timestamp comparisons rely on the newtype
        -- compilation to avoid a hot-path allocation.
        -- If either assumption regresses we want a clear early failure
        -- before ConstructorTest runs.
        need ["build/libaletheia-ffi.so"]
        frame <- liftIO $ readFile "build/MAlonzo/Code/Aletheia/CAN/Frame.hs"
        time  <- liftIO $ readFile "build/MAlonzo/Code/Aletheia/Trace/Time.hs"
        -- Single-Integer ctor shape post-R18 cluster 17 — irrelevant proof
        -- erased; reject any reintroduction of an `AgdaAny` proof slot.
        -- Match by absence of the AgdaAny-shaped form rather than positive
        -- presence: MAlonzo formats the data declaration on one line
        -- (`data T_CANId_8 = C_Standard_12 Integer | C_Extended_16 Integer`),
        -- so a positive-presence check would race the formatter.
        let canIdErasure =
              "C_Standard_12 Integer" `isInfixOf` frame &&
              "C_Extended_16 Integer" `isInfixOf` frame &&
              not ("C_Standard_12 Integer AgdaAny" `isInfixOf` frame) &&
              not ("C_Extended_16 Integer AgdaAny" `isInfixOf` frame)
        unless canIdErasure $
          error $ "check-erasure failed: CAN ID constructor shape drifted "
               ++ "from the post-R18-cluster-17 single-Integer form. "
               ++ "Either MAlonzo regressed and re-emits the proof slot, or "
               ++ "the AGDA-B-22.1 `.(…)` irrelevance was reverted. "
               ++ "Marshal.hs mkAgdaCanId assumes single-arg constructors; "
               ++ "fix the source of drift before this regresses end-to-end."
        let tsNewtype = "newtype T_Timestamp_18" `isInfixOf` time
        unless tsNewtype $
          error $ "check-erasure failed: Timestamp is no longer compiled as "
               ++ "a newtype. Trace/Time.agda uses `record ... no-eta-equality` "
               ++ "intentionally so MAlonzo compiles Timestamp comparisons "
               ++ "without a wrapper allocation on the hot path."
        -- Stdlib constructor names used by BinaryOutput.hs.
        -- These are mangled from stdlib's Vec/Sum modules; a stdlib version
        -- bump can silently rename them, breaking pattern matches at runtime.
        vecBase <- liftIO $ readFile "build/MAlonzo/Code/Data/Vec/Base.hs"
        sumBase <- liftIO $ readFile "build/MAlonzo/Code/Data/Sum/Base.hs"
        let vecCtors =
              "C_'91''93'_32"   `isInfixOf` vecBase &&
              "C__'8759'__38"   `isInfixOf` vecBase
        unless vecCtors $
          error $ "check-erasure failed: Vec stdlib constructor names changed. "
               ++ "BinaryOutput.hs pattern-matches on C_'91''93'_32 (nil) and "
               ++ "C__'8759'__38 (cons) — update to match current MAlonzo output."
        let sumCtors =
              "C_inj'8321'_38"  `isInfixOf` sumBase &&
              "C_inj'8322'_42"  `isInfixOf` sumBase
        unless sumCtors $
          error $ "check-erasure failed: Sum stdlib constructor names changed. "
               ++ "BinaryOutput.hs pattern-matches on C_inj'8321'_38 (inj₁) and "
               ++ "C_inj'8322'_42 (inj₂) — update to match current MAlonzo output."
        -- Maybe / Sigma builtin constructor names used by Marshal.hs +
        -- BinaryOutput.hs.  R19 cluster 13 — AGDA-D-30.1 / AGDA-D-GA23.2:
        -- the FFI shim's `unsafeCoerce` sites assume specific MAlonzo
        -- constructor shapes for Agda.Builtin.Maybe and Agda.Builtin.Sigma;
        -- a stdlib bump or builtin-module rename can drift them silently.
        maybeBase <- liftIO $ readFile "build/MAlonzo/Code/Agda/Builtin/Maybe.hs"
        sigmaBase <- liftIO $ readFile "build/MAlonzo/Code/Agda/Builtin/Sigma.hs"
        let maybeCtors =
              "C_nothing_18" `isInfixOf` maybeBase &&
              "C_just_16"    `isInfixOf` maybeBase
        unless maybeCtors $
          error $ "check-erasure failed: Maybe builtin constructor names "
               ++ "changed. Marshal.hs / BinaryOutput.hs pattern-match on "
               ++ "C_nothing_18 / C_just_16 — update to match current "
               ++ "MAlonzo output."
        let sigmaCtors =
              "T_Σ_14"        `isInfixOf` sigmaBase &&
              "C__'44'__32"   `isInfixOf` sigmaBase &&
              "d_fst_28"      `isInfixOf` sigmaBase &&
              "d_snd_30"      `isInfixOf` sigmaBase
        unless sigmaCtors $
          error $ "check-erasure failed: Sigma builtin constructor / "
               ++ "accessor names changed. Marshal.hs / BinaryOutput.hs "
               ++ "rely on T_Σ_14 / C__'44'__32 / d_fst_28 / d_snd_30 — "
               ++ "update to match current MAlonzo output."
        putInfo "Erasure guards OK: CANId single-Integer ctor + Timestamp newtype + stdlib constructors + Maybe/Sigma builtins."

    phony "check-ffi-exports" $ do
        -- Diff MAlonzo-mangled FFI export names against the checked-in
        -- `haskell-shim/ffi-exports.snapshot`. Guards against silent drift
        -- when Agda definitions are reordered or new definitions are added
        -- above existing exports. Complements `checkFFINames` (run inline
        -- during the Main.hs build rule), which keeps AletheiaFFI.hs in
        -- sync with the mangled names.
        --
        -- R20 cluster I — AGDA-D-30.1.  Each non-blank, non-`#` snapshot
        -- line carries one of three kind prefixes:
        --   * `F: <module>:<name>` — function export (`d_*`).  Validated
        --     by `(name ++ " ::") isInfixOf module-source`.
        --   * `C: <module>:<name>` — data constructor tag (`C_*`).
        --     Validated against the data declaration's alternatives.
        --   * `T: <module>:<name>` — type tag (`T_*`).  Validated against
        --     the `data` / `newtype` declaration header.
        -- Lines with no prefix are treated as `F:` for back-compat with
        -- the pre-R20 snapshot format.
        need ["build/MAlonzo/Code/Aletheia/Main.hs"]
        let snapshotFile = "haskell-shim/ffi-exports.snapshot"
        snapshotContent <- liftIO $ readFile snapshotFile
        let parseSnapshotLine l =
                let s = strip l
                in if null s || "#" `isPrefixOf` s
                   then Nothing
                   else
                     let (kind, body) = case stripPrefix "F: " s of
                                          Just rest -> ("F", rest)
                                          Nothing -> case stripPrefix "C: " s of
                                            Just rest -> ("C", rest)
                                            Nothing -> case stripPrefix "T: " s of
                                              Just rest -> ("T", rest)
                                              Nothing -> ("F", s)  -- back-compat
                     in case break (== ':') body of
                          (m, ':':n) -> Just (kind, m, n)
                          _          -> Nothing
        let expected =
                [ p
                | Just p <- map parseSnapshotLine (lines snapshotContent)
                ]
        -- Load every module mentioned in the snapshot, not just those in
        -- `ffiExports`.  R19 cluster 13 — AGDA-D-30.2 extended the snapshot
        -- to cover indirect helper accessors (Sigma fst/snd, DLC, Rational
        -- numerator/denominator, BatchExtraction values/errors/absent);
        -- R20 cluster I — AGDA-D-30.1 added constructor / type tags for
        -- the load-bearing MAlonzo types that AletheiaFFI.hs constructs
        -- or unsafe-coerces through (StreamState, CANId, DLC, Sum, etc.)
        -- — these are NOT in `ffiExports` because they are not `foreign
        -- export` targets, only their constructor numbering is.
        let snapshotModules = nub [m | (_, m, _) <- expected]
        moduleContents <- liftIO $ forM snapshotModules $ \m -> do
            let path = "build/MAlonzo/Code" </> m <.> "hs"
            existsHere <- SysDir.doesFileExist path
            if existsHere
              then do c <- readFile path; return (m, Just c)
              else return (m, Nothing)
        -- A constructor / type tag is "present" if the mangled name
        -- appears in the expected position in the MAlonzo output.  We
        -- check a small family of contexts to tolerate MAlonzo's
        -- per-version formatting variation.
        let funcPresent name c = (name ++ " ::") `isInfixOf` c
            ctorPresent name c =
                (" " ++ name ++ " ")  `isInfixOf` c
             || (" " ++ name ++ "\n") `isInfixOf` c
             || ("\n" ++ name ++ " ") `isInfixOf` c  -- continuation after `|\n   `
             || ("(" ++ name ++ " ") `isInfixOf` c
             || ("(" ++ name ++ ")") `isInfixOf` c
            typePresent name c =
                ("data "    ++ name ++ " ")  `isInfixOf` c
             || ("data "    ++ name ++ "\n") `isInfixOf` c
             || ("newtype " ++ name ++ " ")  `isInfixOf` c
             || ("newtype " ++ name ++ "\n") `isInfixOf` c
            entryPresent kind name c = case kind of
                "F" -> funcPresent name c
                "C" -> ctorPresent name c
                "T" -> typePresent name c
                _   -> False
        let failures =
              [ (kind, modName, mangled)
              | (kind, modName, mangled) <- expected
              , Just mc <- [lookup modName moduleContents]
              , case mc of
                  Just c  -> not (entryPresent kind mangled c)
                  Nothing -> True
              ]
        unless (null failures) $ do
            forM_ failures $ \(kind, m, expected') ->
                putError $ unlines
                    [ ""
                    , "════════════════════════════════════════════════════════════════"
                    , "ERROR: FFI " ++ kindLabel kind ++ " snapshot drift in " ++ m
                    , "════════════════════════════════════════════════════════════════"
                    , ""
                    , "  Expected (snapshot): " ++ kind ++ ": " ++ m ++ ":" ++ expected'
                    , ""
                    , "  Snapshot file: " ++ snapshotFile
                    , ""
                    , "  If the drift is intentional, regenerate:"
                    , "    cabal run shake -- regen-ffi-exports"
                    , ""
                    , "════════════════════════════════════════════════════════════════"
                    , ""
                    ]
            error "check-ffi-exports failed: snapshot mismatch"
        putInfo $ "FFI exports match snapshot: "
               ++ show (length expected) ++ " entries ("
               ++ show (length [() | ("F", _, _) <- expected]) ++ " functions, "
               ++ show (length [() | ("C", _, _) <- expected]) ++ " constructors, "
               ++ show (length [() | ("T", _, _) <- expected]) ++ " types)."

    phony "regen-ffi-exports" $ do
        -- Rewrite the F: function entries in `haskell-shim/ffi-exports.snapshot`
        -- in-place from the current MAlonzo output.  Run after an intentional
        -- Agda refactor that changes the mangled numbers.
        --
        -- Preservation contract (R20 cluster I follow-up — the original regen
        -- iterated only `ffiExports` and overwrote the whole file, which would
        -- have silently dropped every C: constructor / T: type / indirect F:
        -- helper line on first re-run):
        --
        --   * Lines without an `F: ` prefix (header comments, blanks, section
        --     dividers, `C: …`, `T: …`) are copied through verbatim.
        --   * `F: <module>:d_<funcName>_NN` lines whose `<module>` and
        --     `<funcName>` match an entry in `ffiExports` get their NN
        --     refreshed from MAlonzo.
        --   * `F: …` lines that do NOT match any `ffiExports` entry (the
        --     R19 cluster 13 indirect-helper block) are preserved verbatim.
        --   * If an `ffiExports` entry has no matching `F:` line in the
        --     snapshot (newly added export), we error out with a placeholder
        --     suggestion rather than silently dropping it.
        need ["build/MAlonzo/Code/Aletheia/Main.hs"]
        moduleContents <- loadFFIModuleContents
        let freshFor e = do
                c <- lookup (ffiModule e) moduleContents
                extractMangledName (ffiFuncName e) c
            missingMangle =
                [ ffiFuncName e ++ " (" ++ ffiModule e ++ ")"
                | e <- ffiExports
                , case freshFor e of { Just _ -> False; Nothing -> True }
                ]
        unless (null missingMangle) $
            error $ "regen-ffi-exports: could not extract mangled name for: "
                 ++ unwords missingMangle
        let freshEntries :: [(FFIExport, String)]
            freshEntries =
                [ (e, n) | e <- ffiExports, Just n <- [freshFor e] ]
            rewriteLine line =
                case stripPrefix "F: " line of
                    Nothing   -> (line, Nothing)
                    Just body ->
                        case [ (i, e, n)
                             | (i, (e, n)) <- zip [0 :: Int ..] freshEntries
                             , (ffiModule e ++ ":d_" ++ ffiFuncName e ++ "_")
                                 `isPrefixOf` body
                             ] of
                            ((i, e, n):_) ->
                                ( "F: " ++ ffiModule e ++ ":" ++ n
                                , Just i
                                )
                            [] -> (line, Nothing)  -- indirect helper; preserve
        existing <- liftIO $ do
            c <- readFile "haskell-shim/ffi-exports.snapshot"
            length c `seq` return c  -- force read; we writeFile to same path below
        let (rewrittenLines, hits) =
                unzip (map rewriteLine (lines existing))
            matched = nub [i | Just i <- hits]
            unmatched =
                [ e | (i, (e, _)) <- zip [0 :: Int ..] freshEntries
                    , i `notElem` matched
                ]
        unless (null unmatched) $
            error $ unlines $
                [ "regen-ffi-exports: these ffiExports entries have no F: line"
                , "in the snapshot.  Add a placeholder before re-running:"
                , ""
                ] ++
                [ "    F: " ++ ffiModule e ++ ":d_" ++ ffiFuncName e ++ "_0"
                | e <- unmatched
                ]
        liftIO $ writeFile "haskell-shim/ffi-exports.snapshot"
                           (unlines rewrittenLines)
        putInfo $ "Regenerated snapshot: refreshed "
               ++ show (length matched) ++ " F: function entries; "
               ++ "preserved "
               ++ show (length (lines existing) - length matched)
               ++ " non-function lines (C: / T: / indirect F: helpers / comments)."

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
        -- CHANGELOG discipline enforcement.  Detects notable drift since
        -- merge-base with `main` — the public-API surface (UR-1) PLUS the
        -- build system, CI, and tooling — and fails if CHANGELOG.md was not
        -- also modified.
        --
        -- Implementation lives in tools/check_changelog.py so the same
        -- gate can be invoked from the pre-push hook and from local CI
        -- without rebuilding the Shake binary.  Branch-level granularity
        -- (one CHANGELOG commit covers any number of notable commits
        -- on the same branch).
        cmd_ pythonBin "-m" "tools.check_changelog"

    phony "check-spdx-headers" $ do
        -- SPDX license-header gate.  Every source/build file must carry the
        -- two-line SPDX header (SPDX-FileCopyrightText 2025 Nicolas Pelletier +
        -- SPDX-License-Identifier BSD-2-Clause).  The tool is an allowlist over
        -- source/build extensions and excludes docs, archived review data,
        -- comment-less files (JSON), binaries, and generated artefacts.  Repair
        -- in place with `python -m tools.check_spdx_headers --apply`.
        cmd_ pythonBin "-m" "tools.check_spdx_headers"

    phony "check-gate-claim" $ do
        -- Gate-claim integrity enforcer (R18 cluster 1 phase 2).
        -- Mechanical enforcer for `memory/feedback_gate_claim_integrity.md`.
        -- When a commit message contains a gate-clean assertion ("all gates
        -- clean", "gates green", etc.), verify that build/libaletheia-ffi.so
        -- mtime postdates every build-relevant staged source file's mtime.
        --
        -- Defaults to HEAD-mode when invoked via Shake (pre-commit mode is
        -- only meaningful inside the actual pre-commit hook context).
        cmd_ pythonBin "-m" "tools.check_gate_claim" "HEAD"

    phony "check-runbook" $ do
        -- Runbook coverage gate (R18 cluster 4).  AGENTS.md cat 22 mandates
        -- that every structured log event the bindings emit has a matching
        -- entry in docs/operations/RUNBOOK.md.  This script parses
        -- docs/LOG_EVENTS.yaml and verifies every event name appears as a
        -- `#### `<name>`` heading in the runbook.  Missing entries fail the
        -- gate — operators must not be left blind on an event the code emits.
        cmd_ pythonBin "-m" "tools.check_runbook_coverage"

    phony "check-limits-parity" $ do
        -- Limits SSOT parity gate (post-R20 DEFERRALS sweep).  The Agda
        -- `Aletheia.Limits` module is the single source of truth for every
        -- adversarial-input bound (AGENTS.md universal rule).  The Go
        -- binding mirrors a subset at `go/aletheia/limits.go` for
        -- cgo-boundary pre-rejection — its header claims "mirrored here
        -- verbatim", and this script enforces that promise.  Python and
        -- C++ bindings consume bounds via the typed `InputBoundExceeded`
        -- error returned from the kernel; they have no local mirror and
        -- are out of scope for this gate.  Failing on: missing required
        -- mirror, numeric value mismatch, BoundKind wire-string mismatch,
        -- or any side having an entry the other side lacks (with explicit
        -- categorisation in NAME_MAPPING).
        cmd_ pythonBin "-m" "tools.check_limits_parity"

    phony "check-stability-bench" $ do
        -- Stability-bench coverage gate (R18 cluster 6).  AGENTS.md cat 16 /
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
        -- Mutation-setup coverage gate (R18 cluster 7).  AGENTS.md cat 14(g)
        -- mandates per-binding mutation testing on hot-path modules.  This
        -- script parses docs/MUTATION_BENCH.yaml and verifies every declared
        -- hot-path source file exists on disk — catches silent removal /
        -- rename of a hot-path file (e.g. a future protocols-split move that
        -- relocates `aletheia/client/_client.py`) without running the
        -- mutation tools (each binding's tool takes 30 min - 2 hours).
        -- Dynamic counterpart that actually runs mutmut / go-mutesting /
        -- Mull is `tools/mutation_run.py`, gated behind
        -- ALETHEIA_MUTATION_CHECK=1 (or `--mutation`) in `tools/run_ci.py`.
        cmd_ pythonBin "-m" "tools.check_mutation_setup"

    phony "check-bound-enforcement" $ do
        -- Adversarial-input bound enforcement gate (R20 cluster I /
        -- AGDA-D-32.5).  AGENTS.md universal rule "Adversarial-input bounds
        -- at parser surfaces" requires every `BoundKind` ctor in
        -- `Aletheia.Limits` to surface as a typed
        -- `Error.InputBoundExceeded <Ctor> observed limit` at some parser
        -- or handler boundary.  This script parses the `data BoundKind`
        -- ADT and greps for `InputBoundExceeded <Ctor>` emit sites under
        -- `src/`; a ctor with zero sites is dead metadata (the wire code
        -- is unreachable) and fails the gate.
        cmd_ pythonBin "-m" "tools.check_bound_enforcement"

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
    --   * Direct:    `tools/run_ci.py`     (pre-push hook, manual runs)
    --   * Per-gate:  `cabal run shake -- check-properties` (etc.)

    phony "dist" $ do
        -- CICD-5.2 (R23): dist must NOT ship a tarball that skipped the proof
        -- tree.  Pre-push hook is the canonical defense; bind the proof gates
        -- here too as defense-in-depth so direct `cabal run shake -- dist`
        -- invocations cannot side-step them.  Adds ~10 min to a release cut.
        need ["check-properties",
              "check-invariants",
              "check-no-properties-in-runtime",
              "check-erasure",
              "check-fidelity",
              "check-ffi-exports",
              "build/libaletheia-ffi.so"]

        let distDir = "dist/aletheia"
        let distLib = distDir </> "lib"
        let distInclude = distDir </> "include"
        let tarball = "dist/aletheia.tar.gz"
        let manifestFile = distDir </> "MANIFEST.txt"
        let sbomFile = distDir </> "aletheia-sbom.cdx.json"
        let tarHashFile = tarball ++ ".sha256"
        let tarSigFile = tarball ++ ".sig"

        -- Clean previous dist
        liftIO $ removePathForcibly distDir
        liftIO $ removePathForcibly tarball
        liftIO $ removePathForcibly tarHashFile
        liftIO $ removePathForcibly tarSigFile
        liftIO $ createDirectoryIfMissing True distLib
        liftIO $ createDirectoryIfMissing True distInclude

        -- UR-3.2: record source-side hash (pre-strip, pre-patchelf) — anchors
        -- the chain-of-custody from build/libaletheia-ffi.so to dist tarball.
        sourceHash <- sha256file "build/libaletheia-ffi.so"

        -- Copy main .so and GHC runtime dependencies
        putInfo "Packaging distribution..."
        cmd_ "cp" "build/libaletheia-ffi.so" distLib
        ghcDeps <- getGhcDeps "build/libaletheia-ffi.so"
        forM_ ghcDeps $ \dep ->
            cmd_ "cp" "-L" dep distLib

        let mainSoDist = distLib </> "libaletheia-ffi.so"

        -- CICD-4.1: hash-verify post-copy matches source (catches a transient
        -- copy corruption between unpackaged .so and packaged dist).
        copyHash <- sha256file mainSoDist
        when (copyHash /= sourceHash) $
            error $ "dist: post-copy hash drift (source " ++ sourceHash ++
                    " vs copy " ++ copyHash ++ ")"

        -- CICD-2.1: cache .so file list once instead of two find invocations.
        Stdout rawSoFiles <- cmd Shell ("find " ++ distLib ++ " -name '*.so*' -type f")
        let soFiles = filter (not . null) (lines rawSoFiles)

        -- Patch RUNPATH so all .so files find each other via $ORIGIN
        Exit patchelfCode <- cmd Shell "command -v patchelf >/dev/null 2>&1"
        case patchelfCode of
            ExitSuccess ->
                forM_ soFiles $ \f ->
                    cmd_ "patchelf" "--set-rpath" "$ORIGIN" f
            ExitFailure _ ->
                putWarn "patchelf not found — skipping RPATH patching. Set LD_LIBRARY_PATH at runtime."

        -- Strip debug symbols to reduce size (--strip-unneeded, NOT --strip-all:
        -- --strip-all would remove the C export symbols needed by dlsym)
        Exit stripCode <- cmd Shell "command -v strip >/dev/null 2>&1"
        case stripCode of
            ExitSuccess -> do
                putInfo "Stripping debug symbols..."
                forM_ soFiles $ \f ->
                    cmd_ "strip" "--strip-unneeded" f
            ExitFailure _ ->
                putWarn "strip not found — keeping debug symbols."

        -- Copy C header
        cmd_ "cp" "include/aletheia.h" distInclude

        -- UR-3.2: post-strip / post-patchelf hashes — bytes that ship in the
        -- tarball.  `finalHash` is the load-bearing artifact identity.
        finalHash <- sha256file mainSoDist
        depHashes <- forM soFiles $ \f -> do
            h <- sha256file f
            return (takeFileName f, h)

        -- Toolchain pin metadata.  Build-date is the commit time, NOT the
        -- wall-clock at dist invocation — wall-clock would defeat artifact-
        -- level reproducibility (two dist runs of the same commit would yield
        -- different MANIFEST.txt content → different tarball hash).
        Stdout gitCommit  <- cmd Shell "git rev-parse HEAD"
        Stdout gitDirty   <- cmd Shell "git status --porcelain"
        Stdout commitTime <- cmd Shell "git log -1 --format=%ct HEAD"
        let commitEpoch = strip commitTime
        Stdout buildDate  <- cmd Shell ("date -u -Iseconds -d @" ++ commitEpoch)
        Stdout ghcVer    <- cmd Shell "ghc --numeric-version"
        Stdout cabalVer  <- cmd Shell "cabal --numeric-version"
        -- agda --version emits multi-line output (version + cabal flag list);
        -- take only the first line.
        Stdout agdaVer   <- cmd Shell "agda --version | head -n1"
        Stdout agdaLib   <- cmd Shell "grep '^depend:' aletheia.agda-lib | sed 's/depend://'"
        let gitTreeStatus = if null (strip gitDirty) then "clean" else "dirty"
        let pad n s = s ++ replicate (max 0 (n - length s)) ' '
        let readmeFile = distDir </> "README.txt"
        let readmeText = unlines
                [ "Aletheia"
                , "========"
                , ""
                , "This tarball ships a pre-built Aletheia release artifact."
                , ""
                , "Contents:"
                , "  lib/libaletheia-ffi.so     Verified Agda kernel + GHC runtime"
                , "  lib/libHS*.so              GHC runtime dependencies (RPATH=$ORIGIN)"
                , "  include/aletheia.h         C header (consumed by Python/C++/Go bindings)"
                , "  MANIFEST.txt               Toolchain pin + per-artifact SHA-256 hashes"
                , "  aletheia-sbom.cdx.json     CycloneDX 1.5 software bill of materials"
                , ""
                , "Quick start (from the unpacked tarball):"
                , "  gcc -Iinclude -Llib -Wl,-rpath,'$ORIGIN/../lib' -laletheia-ffi app.c"
                , ""
                , "Verification (verify-then-trust order):"
                , "  1. Tarball signature (cosign + keys/cosign.pub from the source tree)"
                , "  2. sha256sum -c aletheia.tar.gz.sha256"
                , "  3. After unpacking: hashes inside MANIFEST.txt vs find lib -name '*.so*'"
                , ""
                , "Full integration guide:"
                , "  docs/development/DISTRIBUTION.md (in the source repo)"
                , ""
                , "Release process and signing key rotation:"
                , "  docs/development/RELEASE.md (in the source repo)"
                , ""
                , "Build provenance (this artifact):"
                , "  Git commit:  " ++ strip gitCommit
                , "  Git tree:    " ++ gitTreeStatus
                , "  Build date:  " ++ strip buildDate ++ "  (commit time, NOT wall-clock)"
                ]
        liftIO $ writeFile readmeFile readmeText

        let manifestText = unlines $
                [ "Aletheia distribution manifest"
                , "=============================="
                , ""
                , "Generated:   " ++ strip buildDate
                , "Git commit:  " ++ strip gitCommit
                , "Git tree:    " ++ gitTreeStatus
                , ""
                , "Toolchain (pinned for reproducible build):"
                , "  GHC:           " ++ strip ghcVer
                , "  cabal-install: " ++ strip cabalVer
                , "  Agda:          " ++ strip agdaVer
                , "  Agda stdlib:   " ++ strip agdaLib
                , ""
                , "Source artifact (pre-strip, pre-patchelf):"
                , "  build/libaletheia-ffi.so          " ++ sourceHash
                , ""
                , "Distribution artifacts (post-strip, post-patchelf):"
                ] ++ map (\(n, h) -> "  " ++ pad 34 n ++ h) depHashes ++
                [ ""
                , "Verification:"
                , "  Distribution integrity (compare against this manifest):"
                , "    find lib/ -name '*.so*' -exec sha256sum {} \\;"
                , "  Tarball signature (local dev, signed without tlog):"
                , "    cosign verify-blob --insecure-ignore-tlog \\"
                , "      --key keys/cosign.pub \\"
                , "      --signature aletheia.tar.gz.sig aletheia.tar.gz"
                , "  Tarball signature (release, signed with ALETHEIA_COSIGN_TLOG=1):"
                , "    cosign verify-blob --key keys/cosign.pub \\"
                , "      --signature aletheia.tar.gz.sig aletheia.tar.gz"
                , ""
                , "Reference:"
                , "  AGENTS.md § Universal Rules → Reproducible build verification"
                , "  docs/development/RELEASE.md § Verifying release artifacts"
                ]
        liftIO $ writeFile manifestFile manifestText

        -- UR-3.2 / CICD-5.3: SBOM (CycloneDX 1.5).  Pass the git commit epoch
        -- as --source-epoch so the SBOM timestamp + UUID5 are derived from
        -- source state, not wall-clock — required for artifact-level repro.
        putInfo "Generating SBOM..."
        let distGhcDeps = map (\dep -> distLib </> takeFileName dep) ghcDeps
        cmd_ pythonBin "-m" "tools.sbom_generate"
            "--repo" "."
            "--main-so" mainSoDist
            "--out" sbomFile
            "--source-epoch" commitEpoch
            distGhcDeps

        -- Reproducible tarball: sort entries + pin mtime to the git commit time
        -- + zero owner/group.  Use `gzip -n` to suppress gzip's per-invocation
        -- timestamp embed (the gzip header MTIME field defaults to current
        -- wall-clock if -n is not set).  Without these flags `tar czf` embeds
        -- wall-clock mtime, the invoking user's uid/gid, and the gzip wall-
        -- clock — three orthogonal sources defeating tarball-level repro.
        let mtime = "@" ++ commitEpoch
        putInfo $ "Creating reproducible tarball (mtime=" ++ mtime ++ ")..."
        cmd_ "tar"
            "--sort=name"
            ("--mtime=" ++ mtime)
            "--owner=0" "--group=0" "--numeric-owner"
            ("--use-compress-program=gzip -n")
            "-cf" tarball
            "-C" "dist" "aletheia/"

        -- CICD-5.2: side-car SHA-256 for the tarball, suitable for sha256sum -c.
        tarballHash <- sha256file tarball
        liftIO $ writeFile tarHashFile (tarballHash ++ "  " ++ takeFileName tarball ++ "\n")

        -- CICD-5.4: sign the tarball if cosign + key are available.  Skip-with-
        -- warning when either is missing — release verification fails closed
        -- on the consumer side via cosign verify-blob, not here.
        cosignKey <- liftIO $ lookupEnv "ALETHEIA_COSIGN_KEY"
        Exit cosignCode <- cmd Shell "command -v cosign >/dev/null 2>&1"
        sigPresent <- case (cosignCode, cosignKey) of
            (ExitSuccess, Just keyPath) -> do
                -- Default --tlog-upload=false: per-dev-run signing should not
                -- push every artifact hash to the public Sigstore Rekor log.
                -- Release signing opts back in via ALETHEIA_COSIGN_TLOG=1.
                tlogEnv <- liftIO $ lookupEnv "ALETHEIA_COSIGN_TLOG"
                let tlogFlag = case tlogEnv of
                        Just "1" -> "--tlog-upload=true"
                        _        -> "--tlog-upload=false"
                putInfo $ "Signing tarball with cosign (" ++ tlogFlag ++ ")..."
                cmd_ Shell $
                    "COSIGN_PASSWORD=\"${COSIGN_PASSWORD:-}\" cosign sign-blob --yes " ++
                    tlogFlag ++
                    " --key '" ++ keyPath ++ "'" ++
                    " --output-signature '" ++ tarSigFile ++ "'" ++
                    " '" ++ tarball ++ "'"
                return True
            (ExitSuccess, Nothing) -> do
                putWarn $ "ALETHEIA_COSIGN_KEY env var not set — skipping artifact signing.\n" ++
                    "  See docs/development/RELEASE.md § Signing for the canonical key path."
                return False
            (ExitFailure _, _) -> do
                putWarn "cosign not found — skipping artifact signing. Install: see docs/development/RELEASE.md."
                return False

        -- Report
        Stdout distSize <- cmd Shell ("du -sh " ++ distDir ++ " | cut -f1")
        Stdout tarSize <- cmd Shell ("du -sh " ++ tarball ++ " | cut -f1")
        let nDeps = length ghcDeps
        putInfo ""
        putInfo "════════════════════════════════════════════════════════════════"
        putInfo "  Distribution packaged"
        putInfo "════════════════════════════════════════════════════════════════"
        putInfo ""
        putInfo $ "  dist/aletheia/           (" ++ strip distSize ++ ")"
        putInfo $ "    lib/libaletheia-ffi.so   (main library, sha256 " ++ take 12 finalHash ++ "...)"
        putInfo $ "    lib/libHS*.so            (" ++ show nDeps ++ " GHC runtime deps, RPATH=$ORIGIN)"
        putInfo $ "    include/aletheia.h       (C header)"
        putInfo $ "    MANIFEST.txt             (UR-3.2 hashes + toolchain pin)"
        putInfo $ "    aletheia-sbom.cdx.json   (CycloneDX 1.5 SBOM)"
        putInfo $ "    README.txt               (consumer entry point — verification + quick start)"
        putInfo $ "  dist/aletheia.tar.gz     (" ++ strip tarSize ++ ", sha256 " ++ take 12 tarballHash ++ "...)"
        putInfo $ "  dist/aletheia.tar.gz.sha256"
        when sigPresent $
            putInfo $ "  dist/aletheia.tar.gz.sig (cosign signature; verify with keys/cosign.pub)"
        putInfo ""
        putInfo "  Verify:"
        putInfo $ "    sha256sum -c " ++ tarHashFile
        when sigPresent $ do
            putInfo $ "    # Local dev (tlog skipped per --tlog-upload=false at sign time):"
            putInfo $ "    cosign verify-blob --insecure-ignore-tlog --key keys/cosign.pub \\"
            putInfo $ "      --signature " ++ tarSigFile ++ " " ++ tarball
            putInfo $ "    # Release (sign with ALETHEIA_COSIGN_TLOG=1, then verify without --insecure-ignore-tlog)"
        putInfo ""
        putInfo "  Usage (no LD_LIBRARY_PATH needed — RPATH handles resolution):"
        putInfo "    gcc -Idist/aletheia/include -Ldist/aletheia/lib \\"
        putInfo "        -Wl,-rpath,'$ORIGIN/../lib' -laletheia-ffi app.c"
        putInfo ""

    phony "install-python" $ do
        need ["build/libaletheia-ffi.so"]
        -- R19 cluster E2 (CICD-3.1 closure): strip secret env vars
        -- before invoking pip3 so a future CI workflow that wires
        -- this target doesn't leak ambient credentials to the package
        -- index resolver.  Stripped: GitHub Actions auth tokens
        -- (GITHUB_TOKEN / GH_TOKEN / GITHUB_API_URL), Aletheia signing
        -- credentials (ALETHEIA_COSIGN_KEY / ALETHEIA_COSIGN_TLOG),
        -- and the generic CI auth knobs (TWINE_PASSWORD / NPM_TOKEN).
        cmd_ (Cwd "python")
            (RemEnv "GITHUB_TOKEN") (RemEnv "GH_TOKEN")
            (RemEnv "GITHUB_API_URL")
            (RemEnv "ALETHEIA_COSIGN_KEY") (RemEnv "ALETHEIA_COSIGN_TLOG")
            (RemEnv "TWINE_PASSWORD") (RemEnv "NPM_TOKEN")
            "pip3 install -e ."

    phony "docker" $ do
        need ["dist"]
        -- CICD-5.5: tag with both `latest` (moving) AND `<short-sha>` (immutable)
        -- so consumers can pin by commit.  Base image is digest-pinned in
        -- Dockerfile.runtime; the local image tag here is the consumer-facing
        -- handle.
        Stdout shortSha <- cmd Shell "git rev-parse --short HEAD"
        let shaTag = "aletheia:" ++ strip shortSha
        putInfo $ "Building Docker runtime image (tags: aletheia:latest, " ++ shaTag ++ ")..."
        cmd_ "docker" "build"
            "-t" "aletheia:latest"
            "-t" shaTag
            "-f" "Dockerfile.runtime" "."
        Stdout imageSize <- cmd Shell "docker images aletheia:latest --format '{{.Size}}'"

        -- CICD-A-5.4 R23 closure: emit an OCI-image SBOM alongside the
        -- existing dist tarball SBOM.  Three image-layer pins augment the
        -- dist SBOM: the built image's content-addressed SHA-256, the
        -- digest-pinned base image (parsed from `FROM ...@sha256:...`),
        -- and the libgmp10 Debian version (parsed from the `apt-get
        -- install` line).  All three are reproducible-build inputs the
        -- consumer needs to verify image provenance.
        Stdout imageIdRaw <- cmd Shell "docker images aletheia:latest --no-trunc --format '{{.ID}}'"
        Stdout commitTimeRaw <- cmd Shell "git log -1 --pretty=%ct"
        dockerfile <- liftIO $ readFile "Dockerfile.runtime"
        ghcDepsDocker <- getGhcDeps "build/libaletheia-ffi.so"
        let imageId       = strip imageIdRaw
            commitEpochD  = strip commitTimeRaw
            imageBase     = parseFromBase dockerfile
            imageLibgmp   = parseLibgmpVersion dockerfile
            imageSbomFile = "build/docker/aletheia-image-sbom.cdx.json"
            distLibDocker = "dist/aletheia/lib"
            distGhcDepsDocker = map (\dep -> distLibDocker </> takeFileName dep) ghcDepsDocker
        liftIO $ createDirectoryIfMissing True (takeDirectory imageSbomFile)
        putInfo $ "Generating image SBOM (" ++ imageSbomFile ++ ")..."
        cmd_ pythonBin "-m" "tools.sbom_generate"
            "--repo" "."
            "--main-so" (distLibDocker </> "libaletheia-ffi.so")
            "--out" imageSbomFile
            "--source-epoch" commitEpochD
            "--image-id" imageId
            "--image-base" imageBase
            "--image-libgmp" imageLibgmp
            distGhcDepsDocker

        putInfo ""
        putInfo "════════════════════════════════════════════════════════════════"
        putInfo $ "  Docker image: aletheia:latest (" ++ strip imageSize ++ ")"
        putInfo $ "  Pinned tag:   " ++ shaTag
        putInfo $ "  Image ID:     " ++ imageId
        putInfo $ "  Image SBOM:   " ++ imageSbomFile
        putInfo "════════════════════════════════════════════════════════════════"
        putInfo ""
        putInfo "  Run:"
        putInfo "    docker run --rm aletheia:latest python3 -c \\"
        putInfo "      \"from aletheia import AletheiaClient; print('OK')\""
        putInfo $ "  Pin to commit:"
        putInfo $ "    docker run --rm " ++ shaTag ++ " ..."
        putInfo ""

    phony "clean" $ do
        putInfo "Cleaning build artifacts..."
        removeFilesAfter "build" ["//*"]
        removeFilesAfter "src" ["//*.agdai"]
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
        malonzoFiles <- getDirectoryFiles "build" ["MAlonzo//**/*.hs"]
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

    "build/libaletheia-ffi.so" %> \out -> do
        -- HONEST DEPENDENCY GRAPH (see memory/project_build_so_idempotency.md).
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
        need [ "haskell-shim/src/AletheiaFFI.hs"
             , "haskell-shim/src/AletheiaFFI/Marshal.hs"
             , "haskell-shim/src/AletheiaFFI/BinaryOutput.hs"
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
        -- only added to GHC in 9.10, and we pin 9.6.7 (see MANIFEST.txt).
        --
        -- Same-host reproducibility was verified empirically WITHOUT this flag
        -- (R18 cluster 3: two clean builds → bit-identical libaletheia-ffi.so),
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

        -- Find and copy the built .so file
        Stdout soPath <- cmd (Cwd "haskell-shim") Shell
            "find dist-newstyle -name 'libaletheia-ffi.so' -type f | head -1"
        let trimmedPath = strip soPath
        if null trimmedPath
            then error "Could not find libaletheia-ffi.so in dist-newstyle"
            else do
                cmd_ (Cwd "haskell-shim") "cp" trimmedPath ("../" ++ out)
                putInfo $ "Shared library created: " ++ out

    -- =========================================================================
    -- Install / Uninstall targets
    -- =========================================================================

    phony "install" $ do
        need ["build/libaletheia-ffi.so"]

        -- Read PREFIX (default: ~/.local)
        home <- liftIO getHomeDirectory
        prefixEnv <- liftIO $ lookupEnv "PREFIX"
        let prefix = maybe (home </> ".local") id prefixEnv
        configShellEnv <- liftIO $ lookupEnv "CONFIGURE_SHELL"
        let configShell = configShellEnv == Just "1"

        -- Check prerequisites
        checkPrerequisites

        let libDir     = prefix </> "lib" </> "aletheia"
        let docDir     = prefix </> "share" </> "doc" </> "aletheia"
        let exampleDir = prefix </> "share" </> "aletheia" </> "examples"
        let venvDir    = libDir </> "venv"
        let venvPython = venvDir </> "bin" </> "python3"
        let venvPip    = venvDir </> "bin" </> "pip"

        -- Create directory tree
        putInfo $ "Installing to " ++ prefix ++ " ..."
        liftIO $ createDirectoryIfMissing True libDir
        liftIO $ createDirectoryIfMissing True docDir
        liftIO $ createDirectoryIfMissing True exampleDir

        -- Copy main shared library
        putInfo "Copying shared library..."
        cmd_ "cp" "build/libaletheia-ffi.so" libDir

        -- Bundle GHC runtime dependencies (only if not standalone)
        ghcDeps <- getGhcDeps "build/libaletheia-ffi.so"
        if null ghcDeps
            then putInfo "Standalone .so detected — no GHC libraries to bundle."
            else do
                putInfo "Bundling GHC runtime libraries..."
                forM_ ghcDeps $ \dep ->
                    cmd_ "cp" "-L" dep libDir
                -- Patch RUNPATH on all .so files so they find each other via $ORIGIN
                putInfo "Patching RUNPATH on shared libraries..."
                Stdout soFiles <- cmd Shell ("find " ++ libDir ++ " -name '*.so*' -type f")
                forM_ (filter (not . null) (lines soFiles)) $ \f ->
                    cmd_ "patchelf" "--set-rpath" "$ORIGIN" f

        -- Copy C header
        let includeDir = prefix </> "include" </> "aletheia"
        liftIO $ createDirectoryIfMissing True includeDir
        putInfo "Copying C header..."
        cmd_ "cp" "include/aletheia.h" includeDir

        -- Create Python venv
        putInfo "Creating Python virtual environment..."
        cmd_ bootstrapPython "-m" "venv" venvDir
        cmd_ venvPip "install" "--upgrade" "pip" "setuptools" "wheel"

        -- Install aletheia Python package (non-editable)
        putInfo "Installing aletheia Python package..."
        cmd_ venvPip "install" "./python"

        -- Find site-packages and write _install_config.py
        Stdout sitePackages <- cmd venvPython "-c"
            "import site; print(site.getsitepackages()[0])"
        let siteDir = strip sitePackages
        let configFile = siteDir </> "aletheia" </> "_install_config.py"
        let soAbsPath = libDir </> "libaletheia-ffi.so"
        putInfo $ "Writing install config: " ++ configFile
        liftIO $ writeFile configFile $
            "from pathlib import Path\n\nLIBRARY_PATH: Path = Path(" ++ show soAbsPath ++ ")\n"

        -- Copy documentation
        putInfo "Copying documentation..."
        cmd_ Shell ("cp -r docs/* " ++ docDir ++ "/")
        -- Copy root doc files that exist
        forM_ ["README.md", "CONTRIBUTING.md", "LICENSE.md", "LICENSE"] $ \f -> do
            rootDocExists <- doesFileExist f
            when rootDocExists $ cmd_ "cp" f docDir

        -- Copy examples
        putInfo "Copying examples..."
        examplesExist <- doesDirectoryExist "examples"
        when examplesExist $ do
            cmd_ Shell ("cp -r examples/* " ++ exampleDir ++ "/")
            cmd_ Shell ("find " ++ exampleDir ++ " -name '__pycache__' -type d -exec rm -rf {} + 2>/dev/null || true")

        -- Write manifest for uninstall
        let manifestFile = libDir </> "manifest.txt"
        liftIO $ writeFile manifestFile $ unlines
            [ prefix </> "lib" </> "aletheia"
            , prefix </> "share" </> "doc" </> "aletheia"
            , prefix </> "share" </> "aletheia"
            ]

        -- Optionally configure shell aliases
        when configShell $ do
            putInfo "Configuring shell aliases..."
            let venvActivate     = venvDir </> "bin" </> "activate"
            let venvActivateFish = venvDir </> "bin" </> "activate.fish"
            let marker = "# Added by aletheia install"

            -- bash
            let bashrc = home </> ".bashrc"
            bashExists <- doesFileExist bashrc
            when bashExists $ do
                Stdout bashContent <- cmd Shell ("cat " ++ bashrc)
                unless (marker `isInfixOf` bashContent) $ do
                    liftIO $ appendFile bashrc $ unlines
                        [ "", marker
                        , "alias aletheia-env='source " ++ venvActivate ++ "'"
                        ]
                    putInfo $ "  Added alias to " ++ bashrc

            -- zsh
            let zshrc = home </> ".zshrc"
            zshExists <- doesFileExist zshrc
            when zshExists $ do
                Stdout zshContent <- cmd Shell ("cat " ++ zshrc)
                unless (marker `isInfixOf` zshContent) $ do
                    liftIO $ appendFile zshrc $ unlines
                        [ "", marker
                        , "alias aletheia-env='source " ++ venvActivate ++ "'"
                        ]
                    putInfo $ "  Added alias to " ++ zshrc

            -- fish
            let fishConfig = home </> ".config" </> "fish" </> "config.fish"
            fishExists <- doesFileExist fishConfig
            when fishExists $ do
                Stdout fishContent <- cmd Shell ("cat " ++ fishConfig)
                unless (marker `isInfixOf` fishContent) $ do
                    liftIO $ appendFile fishConfig $ unlines
                        [ "", marker
                        , "alias aletheia-env 'source " ++ venvActivateFish ++ "'"
                        ]
                    putInfo $ "  Added alias to " ++ fishConfig

        -- Success banner
        putInfo ""
        putInfo "════════════════════════════════════════════════════════════════"
        putInfo "  Aletheia installed successfully!"
        putInfo "════════════════════════════════════════════════════════════════"
        putInfo ""
        putInfo $ "  Location: " ++ prefix
        putInfo ""
        putInfo "  Activate the environment:"
        putInfo $ "    bash/zsh: source " ++ venvDir </> "bin" </> "activate"
        putInfo $ "    fish:     source " ++ venvDir </> "bin" </> "activate.fish"
        putInfo ""
        putInfo "  Then use:"
        putInfo "    python3 -c \"from aletheia import AletheiaClient; print('OK')\""
        putInfo ""
        putInfo "  Uninstall:"
        putInfo $ "    " ++ (if prefixEnv /= Nothing then "PREFIX=" ++ prefix ++ " " else "")
              ++ "cabal run shake -- uninstall"
        putInfo ""

    phony "uninstall" $ do
        -- Read PREFIX (default: ~/.local)
        home <- liftIO getHomeDirectory
        prefixEnv <- liftIO $ lookupEnv "PREFIX"
        let prefix = maybe (home </> ".local") id prefixEnv
        let manifestFile = prefix </> "lib" </> "aletheia" </> "manifest.txt"

        manifestExists <- doesFileExist manifestFile
        if manifestExists
            then do
                manifestContent <- liftIO $ readFile manifestFile
                let dirs = filter (not . null) (lines manifestContent)
                forM_ dirs $ \dir -> do
                    dirExists <- doesDirectoryExist dir
                    when dirExists $ do
                        putInfo $ "Removing " ++ dir ++ " ..."
                        liftIO $ removeDirectoryRecursive dir
                -- Clean up empty parent dirs
                let shareAletheiaDir = prefix </> "share" </> "aletheia"
                shareExists <- doesDirectoryExist shareAletheiaDir
                when shareExists $
                    liftIO $ removeDirectoryRecursive shareAletheiaDir
                putInfo ""
                putInfo "Aletheia uninstalled successfully."
                putInfo ""
            else do
                putInfo $ "No manifest found at " ++ manifestFile
                putInfo "Nothing to uninstall."
