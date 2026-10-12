-- SPDX-FileCopyrightText: 2025 Nicolas Pelletier
-- SPDX-License-Identifier: BSD-2-Clause
-- | What the rule modules share: trimming, the build's two interpreters,
-- the package version a .cabal declares, the GHC runtime libraries a shared
-- object links, and the MAlonzo symlink cabal reads.
module Shared where

import Development.Shake
import System.Directory (createDirectoryLink, removePathForcibly)
import qualified System.Directory as SysDir
import System.Info (os)
import System.IO.Error (catchIOError)
import Data.List (isPrefixOf, stripPrefix)
import Data.Char (isSpace)
import Control.Monad (unless)

-- | Trim whitespace from both ends of a string
strip :: String -> String
strip = dropWhile isSpace . reverse . dropWhile isSpace . reverse

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

-- | Parse the @version:@ field (e.g. "3.0.0.0") from a .cabal file's contents.
-- cabal builds each package version into a SEPARATE @dist-newstyle@ tree
-- (@aletheia-<VER>/…@), so the built @.so@ must be located under the CURRENT
-- version's tree — locating by bare name picks a stale sibling tree when one
-- lingers from a prior version (see the @build/libaletheia-ffi.so@ rule).
-- Returns "" when absent so the caller can fail loud.
parseCabalVersion :: String -> String
parseCabalVersion contents =
    case [ v | line <- lines contents
             , Just rest <- [stripPrefix "version:" line]
             , let v = strip rest
             , not (null v)
             ]
      of (x:_) -> x
         []    -> ""

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

-- | Interpreters for build tooling.  The project requires Python 3.14 (PEP 758
-- `except A, B` syntax lives in tools/, plus requires-python>=3.14), so bare
-- `python3` -- often still 3.12/3.13 -- would `SyntaxError` on the 3.14-only
-- tools.  Build-tooling invocations therefore run in the dev venv
-- (`python/.venv`), which is 3.14 AND carries the project's runtime deps: some
-- meta-checks `import yaml` (PyYAML), absent from a bare interpreter.  Shake
-- runs with cwd = repo root, so the
-- relative venv path resolves.  `bootstrapPython` is the system 3.14 used only
-- to create venvs and as the version-gate target.
pythonBin :: String
pythonBin = "python/.venv/bin/python3"

bootstrapPython :: String
bootstrapPython = "python3.14"
