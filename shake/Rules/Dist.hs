-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
-- | The release artifacts: the dist bundle, the native packages and the
-- runtime image, with the hashing and signing they share.
module Rules.Dist (distRules) where

import Development.Shake
import Development.Shake.FilePath
import System.Directory (removePathForcibly, createDirectoryIfMissing)
import qualified System.Directory as SysDir
import System.Environment (lookupEnv)
import System.Exit (ExitCode(..))
import Data.List (isInfixOf, stripPrefix)
import Control.Monad (when, unless, forM, forM_)
import Shared

-- | Parse the digest-pinned base image from Dockerfile.runtime.
-- Returns the image reference of the FIRST `FROM` line — the runtime
-- stage's base (e.g. `python:3.14-slim@sha256:...`); later `FROM` lines
-- belong to the throwaway verify stages, which ship no bytes.  Takes only
-- the first token so a `FROM <image> AS <stage>` alias is not captured.
-- Falls back to "unknown" if no `FROM` line is found.
parseFromBase :: String -> String
parseFromBase dockerfile =
    case [ base | l <- lines dockerfile
                , Just rest <- [stripPrefix "FROM " l]
                , base:_ <- [words rest]
                ]
      of (x:_) -> x
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

-- | Compute SHA-256 of a file via the system sha256sum binary.
-- Returns the hex digest only (no path/whitespace).
sha256file :: FilePath -> Action String
sha256file p = do
    Stdout out <- cmd "sha256sum" p
    return $ takeWhile (/= ' ') out

-- | Artifact-signing configuration, resolved from the environment once per
-- rule (cosign presence + the ALETHEIA_COSIGN_* selectors) so every rule
-- that signs release artifacts — the dist tarball, the native packages —
-- resolves the mode by the same policy.  Precedence: keyless (CI, ambient
-- OIDC) wins over the keyring key; absent cosign or neither selector set
-- → unsigned.
data SignConfig = SignConfig
    { scMode :: String        -- ^ "keyless" | "keyed" | "none"
    , scKey  :: Maybe String  -- ^ ALETHEIA_COSIGN_KEY value (key-based path)
    , scTlog :: Maybe String  -- ^ ALETHEIA_COSIGN_TLOG value (keyed tlog opt-in)
    }

resolveSignConfig :: Action SignConfig
resolveSignConfig = do
    Exit cosignPresent <- cmd Shell "command -v cosign >/dev/null 2>&1"
    keylessEnv <- liftIO $ lookupEnv "ALETHEIA_COSIGN_KEYLESS"
    cosignKey  <- liftIO $ lookupEnv "ALETHEIA_COSIGN_KEY"
    tlogEnv    <- liftIO $ lookupEnv "ALETHEIA_COSIGN_TLOG"
    let mode
          | ExitFailure _ <- cosignPresent = "none"
          | keylessEnv == Just "1"         = "keyless"
          | Just _ <- cosignKey            = "keyed"
          | otherwise                      = "none"
    return SignConfig { scMode = mode, scKey = cosignKey, scTlog = tlogEnv }

-- | Sign one artifact with cosign per the resolved signing configuration,
-- emitting a @<path>.sig@ sibling (and, keyless only, the short-lived
-- Fulcio certificate as @<path>.crt@).
--
-- Keyless / Sigstore: the ephemeral signing key is minted from the ambient
-- GitHub Actions OIDC token (needs id-token: write) and discarded after
-- use.  tlog upload stays ON (cosign's keyless default) — the short-lived
-- Fulcio cert is verifiable only via its Rekor transparency-log entry.
--
-- Key-based: default @--tlog-upload=false@ — per-dev-run signing should not
-- push every artifact hash to the public Sigstore Rekor log; release
-- signing opts back in via ALETHEIA_COSIGN_TLOG=1.
--
-- Returns True when a signature was produced.  Unsigned mode warns and
-- returns False — release verification fails closed on the consumer side
-- via cosign verify-blob, not here.
signArtifact :: SignConfig -> FilePath -> Action Bool
signArtifact cfg path = case (scMode cfg, scKey cfg) of
    ("keyless", _) -> do
        putInfo $ "Signing " ++ path ++ " with cosign (keyless / ambient OIDC, tlog on)..."
        cmd_ Shell $
            "cosign sign-blob --yes" ++
            " --output-signature '" ++ path ++ ".sig'" ++
            " --output-certificate '" ++ path ++ ".crt'" ++
            " '" ++ path ++ "'"
        return True
    ("keyed", Just keyPath) -> do
        let tlogFlag = case scTlog cfg of
                Just "1" -> "--tlog-upload=true"
                _        -> "--tlog-upload=false"
        putInfo $ "Signing " ++ path ++ " with cosign (key-based, " ++ tlogFlag ++ ")..."
        cmd_ Shell $
            "COSIGN_PASSWORD=\"${COSIGN_PASSWORD:-}\" cosign sign-blob --yes " ++
            tlogFlag ++
            " --key '" ++ keyPath ++ "'" ++
            " --output-signature '" ++ path ++ ".sig'" ++
            " '" ++ path ++ "'"
        return True
    _ -> do
        putWarn $ path ++ " NOT signed — cosign missing, or neither " ++
            "ALETHEIA_COSIGN_KEYLESS=1 nor ALETHEIA_COSIGN_KEY set.\n" ++
            "  See docs/development/RELEASE.md § Signing."
        return False

-- | The dist, packages and docker targets.
distRules :: Rules ()
distRules = do
    phony "dist" $ do
        -- Release hygiene: prune stale per-version dist-newstyle trees BEFORE the
        -- .so is (re)built below, so a release cut builds from only the current
        -- version's tree.  The build/libaletheia-ffi.so rule already selects the
        -- .so version-aware, but a lingering prior-version tree wastes disk and
        -- is the exact footgun a release path must not carry (a version bump
        -- leaves the previous version's tree behind).
        distCabal <- liftIO $ readFile "haskell-shim/aletheia.cabal"
        let distVer = parseCabalVersion distCabal
        when (null distVer) $
            error "Could not parse `version:` from haskell-shim/aletheia.cabal"
        cmd_ (Cwd "haskell-shim") Shell $
            "for d in dist-newstyle/build/*/*/aletheia-*; do "
            ++ "[ -d \"$d\" ] || continue; "
            ++ "[ \"$(basename \"$d\")\" = 'aletheia-" ++ distVer
            ++ "' ] || rm -rf \"$d\"; done"

        -- CICD-5.2: dist must NOT ship a tarball that skipped the proof
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
        let distBindings = distDir </> "bindings"
        let tarball = "dist/aletheia.tar.gz"
        let manifestFile = distDir </> "MANIFEST.txt"
        let sbomFile = distDir </> "aletheia-sbom.cdx.json"
        let tarHashFile = tarball ++ ".sha256"
        let tarSigFile = tarball ++ ".sig"
        -- Keyless (Sigstore) signing emits a short-lived Fulcio certificate
        -- alongside the signature; the key-based path does not.
        let tarCrtFile = tarball ++ ".crt"

        -- Clean previous dist
        liftIO $ removePathForcibly distDir
        liftIO $ removePathForcibly tarball
        liftIO $ removePathForcibly tarHashFile
        liftIO $ removePathForcibly tarSigFile
        liftIO $ removePathForcibly tarCrtFile
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
        cmd_ "cp" "haskell-shim/include/aletheia.h" distInclude

        -- Stage the four language bindings' LIBRARY files from HEAD (tracked
        -- files only, via `git archive` — deterministic, and it naturally
        -- excludes build junk, the venv, target/, and go.work).  Each binding
        -- is a thin wrapper over lib/libaletheia-ffi.so that a consumer points
        -- at via ALETHEIA_LIB (see env.sh / install.sh).  Python/Go/Rust have
        -- no header+lib form — source IS their library.  --strip-components=1
        -- drops the top-level <lang>/ prefix so files land under
        -- bindings/<name>/.  Passing pathspecs as literal argv (not a shell
        -- string) keeps the `:(exclude)…` magic + globs intact for git.
        -- git archive stages from HEAD, so a dirty worktree ships the COMMITTED
        -- bindings while the .so above came from the worktree — warn so a local
        -- dist does not silently mismatch (a release runs on a clean checkout).
        Stdout dirtyTree <- cmd Shell "git status --porcelain"
        when (not (null (strip dirtyTree))) $
            putWarn $ "dist: working tree is dirty — bindings/ are staged from the " ++
                      "last COMMIT (git archive HEAD); uncommitted binding changes are " ++
                      "NOT in this bundle. Commit them for a matching release."
        putInfo "Staging language bindings (git archive HEAD — tracked-only)..."
        let stageBinding :: String -> [String] -> Action ()
            stageBinding name paths = do
                let dest = distBindings </> name
                let stageTar = "dist" </> (".stage-" ++ name ++ ".tar")
                liftIO $ createDirectoryIfMissing True dest
                cmd_ "git" "archive" ("--output=" ++ stageTar) "HEAD"
                    (paths :: [String])
                cmd_ "tar" "-x" "-C" dest "--strip-components=1" "-f" stageTar
                liftIO $ removePathForcibly stageTar
        stageBinding "python"
            [ "python/pyproject.toml", "python/README.md", "python/aletheia" ]
        stageBinding "cpp"
            [ "cpp/CMakeLists.txt", "cpp/README.md", "cpp/sanitizer-ignorelist.txt"
            , "cpp/include", "cpp/src", "cpp/cmake" ]
        stageBinding "go"
            [ "go/go.mod", "go/go.sum", "go/README.md", "go/aletheia"
            , ":(exclude)go/aletheia/*_test.go", ":(exclude)go/aletheia/testdata" ]
        stageBinding "rust"
            [ "rust/Cargo.toml", "rust/Cargo.lock", "rust/README.md", "rust/src" ]

        -- Consumer entry scripts (self-locating; export ALETHEIA_LIB as an
        -- ABSOLUTE path).  install.{sh,fish} also print how to source
        -- env.{sh,fish} from a shell rc file.  Modes pinned explicitly so the
        -- tarball is byte-reproducible regardless of the checkout's stored
        -- executable bits.
        forM_ ["env.sh", "env.fish", "install.sh", "install.fish"] $ \s ->
            cmd_ "cp" ("packaging" </> s) distDir
        cmd_ "chmod" "0644" (distDir </> "env.sh") (distDir </> "env.fish")
        cmd_ "chmod" "0755" (distDir </> "install.sh") (distDir </> "install.fish")

        -- Ship the license with the redistributable bundle (BSD-2 requires the
        -- copyright notice to travel with redistributions).
        cmd_ "cp" "LICENSE.md" distDir

        -- Staging self-check: each binding must carry its entry file, and
        -- go.work must NOT leak (it would hijack a consumer's Go module
        -- resolution).  Presence is a weak check — the functional smoke test
        -- (unpack, source env.sh, import, construct a backend) lives in the
        -- release workflow; this catches a pathspec typo that drops a binding.
        let bindingEntry = [ ("python", "pyproject.toml")
                           , ("cpp",    "CMakeLists.txt")
                           , ("go",     "go.mod")
                           , ("rust",   "Cargo.toml") ]
        forM_ bindingEntry $ \(bname, entry) -> do
            let f = distBindings </> bname </> entry
            present <- doesFileExist f
            unless present $
                error $ "dist: binding staging incomplete — missing " ++ f
        goWorkLeaked <- doesFileExist (distBindings </> "go" </> "go.work")
        when goWorkLeaked $
            error $ "dist: go.work leaked into the bundle " ++
                    "(would hijack a consumer's Go module resolution)"

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
                , "  include/aletheia.h         C ABI header (C / C++-via-C consumers)"
                , "  bindings/python            Python package (pure ctypes, no build step)"
                , "  bindings/cpp               C++ wrapper (CMake add_subdirectory)"
                , "  bindings/go                Go module (cgo + dlopen)"
                , "  bindings/rust              Rust crate (dlopen)"
                , "  env.sh / env.fish          Source to set ALETHEIA_LIB (bash,zsh / fish)"
                , "  install.sh / install.fish  Print shell + per-language wiring instructions"
                , "  MANIFEST.txt               Toolchain pin + per-artifact SHA-256 hashes"
                , "  aletheia-sbom.cdx.json     CycloneDX 1.5 software bill of materials"
                , "  LICENSE.md                 BSD-2-Clause license text"
                , ""
                , "Quick start (from the unpacked tarball):"
                , "  ./install.sh                # prints how to wire your shell + language"
                , "  # or, for a C program directly against the C ABI:"
                , "  gcc -Iinclude -Llib -Wl,-rpath,'$ORIGIN/../lib' -laletheia-ffi app.c"
                , ""
                , "Verification (verify-then-trust order):"
                , "  1. Tarball signature — see MANIFEST.txt Verification for the exact cosign"
                , "     command (key-based or keyless, matching how this build was signed)"
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

        -- Resolve the signing mode ONCE, up front, so the verify command
        -- embedded in MANIFEST.txt matches the signature the tarball actually
        -- carries.  A keyless tarball must NOT tell its consumer to run
        -- `--key cosign.pub` (wrong material for that artifact), and vice versa.
        signCfg <- resolveSignConfig
        let signMode = scMode signCfg

        -- The key-based verify command must match how THIS tarball was signed:
        -- cosign checks the Rekor tlog by default, so a build signed WITHOUT
        -- tlog (ALETHEIA_COSIGN_TLOG≠1 — the dev default) must be verified with
        -- --insecure-ignore-tlog.  Keyless always uploads to tlog (no flag).
        let keyedTlog = case scTlog signCfg of
              Just "1" -> ""
              _        -> "--insecure-ignore-tlog "

        -- Mode-specific verify recipe embedded in MANIFEST.txt.  The keyless
        -- identity regexp pins the release workflow + a v-prefixed TAG ref: only
        -- tag-published releases are trusted (a workflow_dispatch dry-run signs
        -- under refs/heads/… and is deliberately NOT accepted by this recipe).
        let verifyLines = case signMode of
              "keyless" ->
                [ "  Tarball signature (keyless release, v* tag — Sigstore / GitHub Actions OIDC):"
                , "    cosign verify-blob \\"
                , "      --certificate aletheia.tar.gz.crt \\"
                , "      --signature aletheia.tar.gz.sig \\"
                , "      --certificate-identity-regexp \\"
                , "        '^https://github\\.com/Jaetan/aletheia/\\.github/workflows/release\\.yml@refs/tags/v' \\"
                , "      --certificate-oidc-issuer https://token.actions.githubusercontent.com \\"
                , "      aletheia.tar.gz"
                ]
              "keyed" ->
                [ "  Tarball signature (key-based — keys/cosign.pub from the source tree):"
                , "    cosign verify-blob " ++ keyedTlog ++ "--key keys/cosign.pub \\"
                , "      --signature aletheia.tar.gz.sig aletheia.tar.gz"
                ]
              _ ->
                [ "  Tarball signature: UNSIGNED (no cosign on PATH, or neither"
                , "    ALETHEIA_COSIGN_KEYLESS=1 nor ALETHEIA_COSIGN_KEY set at build time)."
                , "    A release build MUST be signed — treat an unsigned tarball as untrusted."
                ]

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
                ] ++ verifyLines ++
                [ ""
                , "Reference:"
                , "  AGENTS.md § Universal Rules → Reproducible build verification"
                , "  docs/development/RELEASE.md § Verifying release artifacts"
                ]
        liftIO $ writeFile manifestFile manifestText

        -- UR-3.2 / CICD-5.3: SBOM (CycloneDX 1.5).  Pass the git commit epoch
        -- as --source-epoch so the SBOM timestamp + UUID5 are derived from
        -- source state, not wall-clock — required for artifact-level repro.
        -- --bindings-dir points at the STAGED bindings tree so the bill also
        -- covers the bundled binding source trees' declared dependencies
        -- (the SBOM must describe the bytes that ship, not the worktree).
        putInfo "Generating SBOM..."
        let distGhcDeps = map (\dep -> distLib </> takeFileName dep) ghcDeps
        cmd_ pythonBin "-m" "tools.sbom_generate"
            "--repo" "."
            "--main-so" mainSoDist
            "--out" sbomFile
            "--source-epoch" commitEpoch
            "--bindings-dir" distBindings
            distGhcDeps

        -- SBOM coverage gate: re-parse the staged binding manifests and assert
        -- every dependency they declare appears in the SBOM just written.
        -- Fail-loud like the staging self-check above (cmd_ aborts the dist on
        -- a non-zero exit).
        cmd_ pythonBin "-m" "tools.check_sbom_coverage"
            "--sbom" sbomFile
            "--bindings" distBindings

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

        -- CICD-5.4: sign the tarball per the signing mode resolved above
        -- (signArtifact emits the .sig — and, keyless, .crt — siblings whose
        -- paths the cleanup at the top of this rule removed).  Skip-with-warning
        -- when unsigned — release verification fails closed on the consumer
        -- side via cosign verify-blob, not here.
        sigPresent <- signArtifact signCfg tarball

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
        putInfo $ "    include/aletheia.h       (C ABI header)"
        putInfo $ "    bindings/{python,cpp,go,rust}   (language wrappers over the .so)"
        putInfo $ "    env.sh env.fish install.sh install.fish   (ALETHEIA_LIB + wiring)"
        putInfo $ "    MANIFEST.txt             (UR-3.2 hashes + toolchain pin)"
        putInfo $ "    aletheia-sbom.cdx.json   (CycloneDX 1.5 SBOM)"
        putInfo $ "    README.txt               (consumer entry point — verification + quick start)"
        putInfo $ "    LICENSE.md               (BSD-2-Clause license text)"
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

    -- Native OS packages (.deb + .rpm) over the SAME payload the release
    -- tarball ships: packaging/nfpm.yaml maps the staged dist/aletheia tree
    -- wholesale to /opt/aletheia (a single `type: tree` entry — the payload
    -- SSOT; never a second file list).  A separate target on purpose: a local
    -- `cabal run shake -- dist` stays nfpm-free, and only the release
    -- workflow adds `packages` on top.
    --
    -- The packages are hash-pinned per release (each gets a .sha256 sidecar
    -- and a cosign signature), NOT claimed bit-reproducible.  Empirically
    -- probed (nfpm 2.47.0, both formats): without SOURCE_DATE_EPOCH two
    -- back-to-back packagings of the SAME staged tree already differ (nfpm
    -- stamps wall-clock into package metadata); with SOURCE_DATE_EPOCH set
    -- both formats ARE bit-identical across re-packagings of the same tree,
    -- but nfpm does not clamp the payload files' mtimes to the epoch, so a
    -- re-staged dist/aletheia tree (fresh `shake dist`) still yields
    -- different package bytes.  End-to-end repro would additionally need the
    -- staging tree's mtimes normalized; until then consumers verify the
    -- pinned hash + signature, not a rebuild.
    phony "packages" $ do
        need ["dist"]

        -- nfpm is a hard requirement here (unlike cosign, which degrades to
        -- unsigned-with-warning): a packages invocation without nfpm could
        -- only produce nothing.  Install is SHA-pinned, like cosign's.
        Exit nfpmPresent <- cmd Shell "command -v nfpm >/dev/null 2>&1"
        case nfpmPresent of
            ExitSuccess -> return ()
            ExitFailure _ -> error $
                "packages: nfpm not found on PATH — install the SHA-pinned " ++
                "release from https://github.com/goreleaser/nfpm/releases " ++
                "(see packaging/nfpm.yaml for the pinned version + sha256)."

        -- Same version parse the dist rule uses: the package version is the
        -- cabal-parsed distVer, injected into packaging/nfpm.yaml via the
        -- NFPM_VERSION environment variable — one authority, no drift.
        pkgCabal <- liftIO $ readFile "haskell-shim/aletheia.cabal"
        let pkgVer = parseCabalVersion pkgCabal
        when (null pkgVer) $
            error "Could not parse `version:` from haskell-shim/aletheia.cabal"

        -- Explicit conventional file names (deb: name_version_arch; rpm:
        -- name-version-release.arch with nfpm's default release of 1) so this
        -- rule knows exactly which files to self-check, hash, and sign.
        let debFile = "dist/aletheia_" ++ pkgVer ++ "_amd64.deb"
        let rpmFile = "dist/aletheia-" ++ pkgVer ++ "-1.x86_64.rpm"

        -- Release hygiene: a version bump would otherwise leave the prior
        -- version's packages (and their sidecars) in dist/ — prune every
        -- package artifact, not just the current names.
        cmd_ Shell $ "rm -f dist/*.deb dist/*.rpm" ++
            concat [ " dist/*." ++ fmt ++ ext
                   | fmt <- ["deb", "rpm"]
                   , ext <- [".sha256", ".sig", ".crt"] ]

        -- SOURCE_DATE_EPOCH = commit time, matching the dist rule's stance
        -- that artifact metadata derives from source state, never wall-clock.
        -- Empirically it pins nfpm's own metadata timestamps in both formats
        -- (see the reproducibility note on this rule) — e.g. the rpm Build
        -- Date becomes the commit time.
        Stdout pkgCommitTime <- cmd Shell "git log -1 --format=%ct HEAD"
        let pkgEpoch = strip pkgCommitTime

        forM_ [("deb", debFile), ("rpm", rpmFile)] $ \(fmt, out) -> do
            putInfo $ "Packaging " ++ out ++ " (nfpm, payload = dist/aletheia -> /opt/aletheia)..."
            cmd_ (AddEnv "NFPM_VERSION" pkgVer)
                (AddEnv "SOURCE_DATE_EPOCH" pkgEpoch)
                "nfpm" "package" "-f" "packaging/nfpm.yaml" "-p" fmt "-t" out

        -- Self-check with teeth (mirrors the dist staging self-check): both
        -- packages must exist non-empty, and the packed payload must carry
        -- the kernel .so under /opt/aletheia/lib — a wrong `src:` in
        -- packaging/nfpm.yaml or a silently-empty tree map fails the build
        -- here, not at a consumer's install.
        forM_ [debFile, rpmFile] $ \p -> do
            present <- doesFileExist p
            unless present $
                error $ "packages: " ++ p ++ " was not produced"
            size <- liftIO $ SysDir.getFileSize p
            when (size <= 0) $
                error $ "packages: " ++ p ++ " is empty"
        Stdout debContents <- cmd "dpkg-deb" "--contents" debFile
        unless ("./opt/aletheia/lib/libaletheia-ffi.so" `isInfixOf` debContents) $
            error $ "packages: " ++ debFile ++
                " does not list the kernel .so under /opt/aletheia/lib — " ++
                "the packaging/nfpm.yaml contents map no longer covers the staged tree"
        -- Same payload assertion for the .rpm when rpm is available (the
        -- release runner has it; both formats pack the same contents map, so
        -- the .deb check above already guards the mapping itself).
        Exit rpmPresent <- cmd Shell "command -v rpm >/dev/null 2>&1"
        case rpmPresent of
            ExitSuccess -> do
                Stdout rpmContents <- cmd "rpm" "-qlp" rpmFile
                unless ("/opt/aletheia/lib/libaletheia-ffi.so" `isInfixOf` rpmContents) $
                    error $ "packages: " ++ rpmFile ++
                        " does not list the kernel .so under /opt/aletheia/lib"
            ExitFailure _ ->
                putWarn $ "packages: rpm not on PATH — skipped the .rpm payload " ++
                    "listing self-check (the .deb payload check covers the shared " ++
                    "contents map; install rpm to close this leg locally)."

        -- Hash-pin + sign each package, exactly like the tarball: a .sha256
        -- sidecar (sha256sum -c compatible) and a cosign signature per the
        -- resolved signing mode.
        pkgCfg <- resolveSignConfig
        pkgHashes <- forM [debFile, rpmFile] $ \p -> do
            h <- sha256file p
            liftIO $ writeFile (p ++ ".sha256") (h ++ "  " ++ takeFileName p ++ "\n")
            _ <- signArtifact pkgCfg p
            return (takeFileName p, h)

        putInfo ""
        putInfo "════════════════════════════════════════════════════════════════"
        putInfo "  Native packages built (payload = the dist bundle at /opt/aletheia)"
        putInfo "════════════════════════════════════════════════════════════════"
        putInfo ""
        forM_ pkgHashes $ \(n, h) ->
            putInfo $ "  dist/" ++ n ++ "  (sha256 " ++ take 12 h ++ "...)"
        putInfo ""
        putInfo "  Install (opt-in env — no maintainer scripts, no profile.d):"
        putInfo $ "    sudo dpkg -i " ++ debFile ++ "      # Debian/Ubuntu (needs libgmp10)"
        putInfo $ "    sudo rpm -i " ++ rpmFile ++ "   # RPM distros (needs the libgmp runtime)"
        putInfo "    source /opt/aletheia/env.sh    # bash/zsh (fish: env.fish)"
        putInfo ""

    phony "docker" $ do
        need ["dist"]
        -- CICD-5.5: tag with both `latest` (moving) AND `<short-sha>` (immutable)
        -- so consumers can pin by commit.  Base image is digest-pinned in
        -- Dockerfile.runtime; the local image tag here is the consumer-facing
        -- handle.
        --
        -- The image build itself carries the cross-binding smoke: the
        -- Dockerfile.runtime throwaway verify stages build the bundled Rust and C++
        -- bindings and build+RUN a Go consumer against the image's own
        -- /opt/aletheia, and the final stage force-depends on all three — so
        -- `docker build` failing IS the gate.  The Python smoke (FFIBackend
        -- construction against the packaged .so) runs inside the runtime
        -- stage.  Requires BuildKit (default since Docker 23).
        Stdout shortSha <- cmd Shell "git rev-parse --short HEAD"
        let shaTag = "aletheia:" ++ strip shortSha
        putInfo $ "Building Docker runtime image (tags: aletheia:latest, " ++ shaTag ++ ")..."
        cmd_ "docker" "build"
            "-t" "aletheia:latest"
            "-t" shaTag
            "-f" "Dockerfile.runtime" "."
        Stdout imageSize <- cmd Shell "docker images aletheia:latest --format '{{.Size}}'"

        -- Emit an OCI-image SBOM alongside the existing dist tarball
        -- SBOM.  Three image-layer pins augment the
        -- dist SBOM: the built image's content-addressed SHA-256, the
        -- digest-pinned base image (parsed from `FROM ...@sha256:...`),
        -- and the libgmp10 Debian version (parsed from the `apt-get
        -- install` line).  All three are reproducible-build inputs the
        -- consumer needs to verify image provenance.  The image now also
        -- ships the four binding source trees under /opt/aletheia/bindings;
        -- adding them as SBOM components is a follow-up — this SBOM covers
        -- the kernel .so closure + image-layer pins only.
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
