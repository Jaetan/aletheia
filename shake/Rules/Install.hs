-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
-- | Installing under a prefix the library, its C header, a venv holding the
-- Python package, the documentation and the examples; removing what the
-- install's manifest lists; and the editable Python install.
module Rules.Install (installRules) where

import Development.Shake
import Development.Shake.FilePath
import System.Directory (removePathForcibly, getHomeDirectory,
                         createDirectoryIfMissing, removeDirectoryRecursive)
import System.Environment (lookupEnv)
import System.Exit (ExitCode(..))
import Data.List (isInfixOf)
import Control.Monad (when, unless, forM_)
import Shared

-- | Check that patchelf and Python 3.14+ are available.
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

-- | The install, uninstall and install-python targets.
installRules :: Rules ()
installRules = do
    phony "install-python" $ do
        need ["build/libaletheia-ffi.so"]
        -- CICD-3.1 closure: strip secret env vars
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

        -- Purge shared libs from any prior install before re-staging: a GHC
        -- toolchain bump changes the bundled libHS*.so sonames, so the old
        -- ones (absent from the new dependency list) are never overwritten and
        -- would accumulate as unreferenced dead weight.  All current .so are
        -- re-copied below; -maxdepth 1 leaves the venv's own .so untouched.
        putInfo "Purging shared libraries from any prior install..."
        cmd_ Shell ("find '" ++ libDir ++ "' -maxdepth 1 -name '*.so*' -type f -delete")

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
                Stdout soFiles <- cmd Shell ("find '" ++ libDir ++ "' -maxdepth 1 -name '*.so*' -type f")
                forM_ (filter (not . null) (lines soFiles)) $ \f ->
                    cmd_ "patchelf" "--set-rpath" "$ORIGIN" f

        -- Copy C header
        let includeDir = prefix </> "include" </> "aletheia"
        liftIO $ createDirectoryIfMissing True includeDir
        putInfo "Copying C header..."
        cmd_ "cp" "haskell-shim/include/aletheia.h" includeDir

        -- Create Python venv
        putInfo "Creating Python virtual environment..."
        cmd_ bootstrapPython "-m" "venv" venvDir
        cmd_ venvPip "install" "--upgrade" "pip" "setuptools" "wheel"

        -- Install aletheia Python package (non-editable)
        putInfo "Installing aletheia Python package..."
        cmd_ venvPip "install" "./python"

        -- Find site-packages and write _install_config.py.  The -c program
        -- must be passed as a LIST element: Shake's `cmd` word-splits bare
        -- String arguments, which sent python the lone word "import" and
        -- made every install since 2026-02-08 die exactly here — after the
        -- library/package copies but before this config write (a partial
        -- install with no _install_config.py).
        Stdout sitePackages <- cmd venvPython
            ["-c", "import site; print(site.getsitepackages()[0])"]
        let siteDir = strip sitePackages
        let configFile = siteDir </> "aletheia" </> "_install_config.py"
        let soAbsPath = libDir </> "libaletheia-ffi.so"
        putInfo $ "Writing install config: " ++ configFile
        liftIO $ writeFile configFile $
            "from pathlib import Path\n\nLIBRARY_PATH: Path = Path(" ++ show soAbsPath ++ ")\n"

        -- Record where this tree installed to (repo-local, gitignored).
        -- tools/check_install_freshness.py reads this instead of guessing
        -- PREFIX — a custom-prefix install stays visible to the gate even
        -- when PREFIX is no longer exported.  `uninstall` removes it.
        liftIO $ writeFile ".install-receipt" $ unlines
            [ prefix
            , soAbsPath
            , configFile
            ]

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
                -- Drop the repo-local install receipt so the freshness gate
                -- stops tracking the removed install.
                liftIO $ removePathForcibly ".install-receipt"
                putInfo ""
                putInfo "Aletheia uninstalled successfully."
                putInfo ""
            else do
                putInfo $ "No manifest found at " ++ manifestFile
                putInfo "Nothing to uninstall."
