import Development.Shake
import Development.Shake.FilePath
import System.Directory (createDirectoryLink, removePathForcibly, doesDirectoryExist)
import System.Info (os)

main :: IO ()
main = shakeArgs shakeOptions{shakeFiles="build", shakeThreads=0} $ do

    phony "build" $ do
        need ["build/aletheia"]

    phony "build-agda" $ do
        need ["build/MAlonzo/Code/Aletheia/Main.hs"]

    phony "build-haskell" $ do
        need ["build/aletheia"]

    phony "install-python" $ do
        need ["build/aletheia"]
        cmd_ (Cwd "python") "pip3 install -e ."

    phony "clean" $ do
        putInfo "Cleaning build artifacts..."
        removeFilesAfter "build" ["//*"]
        removeFilesAfter "src" ["//*.agdai"]
        removeFilesAfter "haskell-shim" ["//MAlonzo"]
        cmd_ (Cwd "haskell-shim") "cabal clean"

    "build/MAlonzo/Code/Aletheia/Main.hs" %> \out -> do
        agdaSources <- getDirectoryFiles "src" ["//*.agda"]
        need (map ("src" </>) agdaSources)

        putInfo "Compiling Agda to Haskell (this may take a few minutes)..."
        cmd_ (Cwd "src")
            "agda"
            "--compile"
            "--compile-dir=../build"
            "--ghc-dont-call-ghc"
            "Aletheia/Main.agda"

        exists <- doesFileExist out
        if exists
            then putInfo $ "MAlonzo output generated: " ++ out
            else error $ "Agda compilation failed: " ++ out ++ " not created"

    phony "create-symlink" $ do
        need ["build/MAlonzo/Code/Aletheia/Main.hs"]

        let symlinkPath = "haskell-shim/MAlonzo"
        let target = "../build/MAlonzo"

        -- Remove existing symlink/directory if present
        liftIO $ removePathForcibly symlinkPath

        putInfo $ "Creating symlink: " ++ symlinkPath ++ " -> " ++ target

        if os == "mingw32"
            then cmd_ "cmd" "/c" "mklink /D" symlinkPath target
            else liftIO $ createDirectoryLink target symlinkPath

    "build/aletheia" %> \out -> do
        need ["build/MAlonzo/Code/Aletheia/Main.hs"]
        need ["create-symlink"]  -- Depend on phony target, not directory
        need ["haskell-shim/src/Main.hs", "haskell-shim/aletheia.cabal"]

        putInfo "Building Haskell executable..."
        cmd_ (Cwd "haskell-shim") "cabal" "build" "exe:aletheia"

        putInfo "Copying binary..."
        cmd_ (Cwd "haskell-shim") Shell
            "cp $(cabal list-bin exe:aletheia) ../build/aletheia"

        putInfo $ "Binary created: " ++ out
