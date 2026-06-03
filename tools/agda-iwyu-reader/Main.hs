-- agda-iwyu-reader (Agda IWYU, Route A): read each .agdai given as an argument
-- and emit, as one JSON object per line (JSONL), the elaboration-complete set of
-- QNames its definitions reference -- each tagged with the (file, pos) binding
-- site of the referenced definition, so the Python driver can match against the
-- highlighting sieve's `definitionSite` def-ids.
--
-- `namesIn (iSignature)` walks the fully-elaborated internal terms, so the
-- used-set includes the instance/implicit/literal-backed uses that surface
-- highlighting cannot see (the inferred-use false-positive class).
--
-- Include paths (project src + stdlib src) come from $AGDA_IWYU_INCLUDE_PATHS
-- (colon-separated); they MUST match what wrote the interface, or `decode`
-- fails (it resolves module<->source via the include dirs).
module Main (main) where

import           Data.Foldable (toList)
import           Data.List (intercalate)
import qualified Data.Set as Set
import           System.Environment (getArgs, lookupEnv)
import           System.IO (hSetEncoding, stdout, utf8)

import           Agda.Interaction.FindFile (mkInterfaceFile)
import           Agda.Interaction.Imports (readInterface)
import           Agda.Interaction.Options (defaultOptions, optIncludePaths)
import           Agda.Syntax.Abstract.Name (QName, nameBindingSite, qnameName)
import           Agda.Syntax.Common.Pretty (prettyShow)
import           Agda.Syntax.Internal.Names (namesIn)
import           Agda.Syntax.Position (posPos, rStart, rangeFilePath, srcFile)
import           Agda.TypeChecking.Monad.Base
                   (Interface, iModuleName, iSignature, runTCMTop, sigDefinitions)
import           Agda.TypeChecking.Monad.Options (setCommandLineOptions)
import           Agda.Utils.FileName (absolute, filePath)
import           Agda.Utils.Lens ((^.))
import qualified Agda.Utils.Maybe.Strict as Strict

main :: IO ()
main = do
  hSetEncoding stdout utf8
  incs  <- maybe [] (filter (not . null) . splitColon) <$> lookupEnv "AGDA_IWYU_INCLUDE_PATHS"
  files <- getArgs
  mapM_ (processFile incs) files

processFile :: [FilePath] -> FilePath -> IO ()
processFile incs path = do
  apath <- absolute path
  mfile <- mkInterfaceFile apath
  case mfile of
    Nothing    -> putStrLn (errObj path "no interface file")
    Just ifile -> do
      let opts = defaultOptions { optIncludePaths = incs }
      res <- runTCMTop (setCommandLineOptions opts >> readInterface ifile)
      case res of
        Left _err          -> putStrLn (errObj path "type-checking error")
        Right Nothing      -> putStrLn (errObj path "decode failed")
        Right (Just iface) -> putStrLn (usedObj path iface)

-- | Binding site (def file, 1-based char offset) of a QName, matching the
-- highlighting `definitionSite` coordinate, when it has a source position.
qnameDefSite :: QName -> Maybe (FilePath, Int)
qnameDefSite q = do
  pos <- rStart (nameBindingSite (qnameName q))
  rf  <- Strict.toLazy (srcFile pos)
  pure (filePath (rangeFilePath rf), fromIntegral (posPos pos))

usedObj :: FilePath -> Interface -> String
usedObj path iface =
  jsonObj
    [ ("path",   jsonStr path)
    , ("module", jsonStr (prettyShow (iModuleName iface)))
    , ("used",   jsonArr (map usedEntry (Set.toList used)))
    ]
  where
    used :: Set.Set QName
    used = namesIn (toList (iSignature iface ^. sigDefinitions))
    usedEntry q = case qnameDefSite q of
      Just (f, p) -> jsonObj [("n", jsonStr (prettyShow q)), ("f", jsonStr f), ("p", jsonNum p)]
      Nothing     -> jsonObj [("n", jsonStr (prettyShow q))]

errObj :: FilePath -> String -> String
errObj path msg = jsonObj [("path", jsonStr path), ("error", jsonStr msg)]

-- ---- tiny JSON encoder (output is strings / ints / arrays / objects) --------

jsonStr :: String -> String
jsonStr s = '"' : concatMap esc s ++ "\""
  where
    esc '"'  = "\\\""
    esc '\\' = "\\\\"
    esc '\n' = "\\n"
    esc '\r' = "\\r"
    esc '\t' = "\\t"
    esc c    = [c]  -- Agda names are printable UTF-8; emit raw

jsonNum :: Int -> String
jsonNum = show

jsonArr :: [String] -> String
jsonArr xs = "[" ++ intercalate "," xs ++ "]"

jsonObj :: [(String, String)] -> String
jsonObj kvs = "{" ++ intercalate "," [jsonStr k ++ ":" ++ v | (k, v) <- kvs] ++ "}"

splitColon :: String -> [String]
splitColon s = case break (== ':') s of
  (a, ':' : rest) -> a : splitColon rest
  (a, _)          -> [a]
