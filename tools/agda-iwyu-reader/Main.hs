{-# LANGUAGE PatternSynonyms #-}
-- agda-iwyu-reader (Agda IWYU, Route A): scope-aware "is this import used?" from
-- the .agdai interfaces.  Reads tab-separated query lines from stdin
--     <consumerAgdai> \t <module> \t <name>
-- and emits one JSON object per query on stdout (JSONL):
--     {"path":<agdai>,"mod":<module>,"name":<name>,"verdict":"USED"|"DEAD"|"UNRESOLVED"}
-- For a renamed import (`renaming (orig to new)`) the driver passes the ORIGINAL
-- name -- the elaborated term references the origin, never the alias.
--
-- The verdict rule (validated against a synthetic fixture matrix; see
-- tools/agda-iwyu-reader/test/): a scope QName q is USED iff
--   (1) q in the used-set  (= namesIn over the consumer signature: covers direct
--       defs, re-exports, datatype/constructor copies, and any name the
--       elaborated term references by its own QName -- including instance /
--       implicit / literal-backed uses that source highlighting cannot see), OR
--   (2) q is a module-application Function COPY whose delegated origin reaches
--       the used-set.  A copy's body is `Def origin <section-args>`; we take the
--       clause-body HEAD (dropping the type and the args, which would otherwise
--       leak unrelated QNames -- the false-"used" trap) and recurse.
-- def q is read from q's OWN defining interface, auto-derived from its
-- qnameModule (the file boundary is unmarked, so strip-retry the module-name
-- prefix until one resolves AND contains q), cached by path.
--
-- UNRESOLVED is returned when the reader cannot decide precisely (defining
-- interface unreadable; pattern synonyms, which live in iPatternSyns and expand
-- to constructors; abstract copies with no clause body).  UNRESOLVED MUST be
-- treated by the driver as "route to the recompile-confirm oracle", never as
-- DEAD -- the no-false-negative guarantee rests on that.
--
-- Include paths (project src + stdlib src) come from $AGDA_IWYU_INCLUDE_PATHS
-- (colon-separated); they MUST match what wrote the interfaces.
module Main (main) where

import           Control.Monad (forM)
import           Control.Monad.IO.Class (liftIO)
import           Data.Foldable (toList)
import qualified Data.HashMap.Strict as HMap
import           Data.IORef
import           Data.List (intercalate)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe (fromMaybe)
import           Data.Set (Set)
import qualified Data.Set as Set
import           System.Environment (lookupEnv)
import           System.IO (hSetEncoding, stdout, utf8)

import           Agda.Interaction.FindFile (findFile', mkInterfaceFile, toIFile)
import           Agda.Interaction.Imports (readInterface)
import           Agda.Interaction.Options (defaultOptions, optIncludePaths)
import           Agda.Syntax.Abstract.Name (ModuleName (..), QName, qnameModule)
import           Agda.Syntax.Common.Pretty (prettyShow)
import qualified Agda.Syntax.Concrete.Name as C
import           Agda.Syntax.Internal (Abs (..), Clause (..), ConHead (..), Term (..))
import           Agda.Syntax.Internal.Names (namesIn)
import           Agda.Syntax.Scope.Base (AbstractName (..), Scope, allNamesInScope, scopeModules)
import           Agda.Syntax.TopLevelModuleName (rawTopLevelModuleNameForModuleName)
import           Agda.TypeChecking.Monad.Base
                   (Definition, Interface, TCM, defCopy, funClauses, iInsideScope, iSignature,
                    pattern Function, runTCMTop, sigDefinitions, theDef)
import           Agda.TypeChecking.Monad.Options (setCommandLineOptions)
import           Agda.TypeChecking.Monad.State (topLevelModuleName)
import           Agda.Utils.FileName (AbsolutePath, absolute, filePath)
import           Agda.Utils.Lens ((^.))
import           Agda.Utils.List1 (List1)
import qualified Agda.Utils.List1 as List1

-- ---- three-valued verdict ---------------------------------------------------

data V = Used | Dead | Unresolved deriving (Eq)

verdictStr :: V -> String
verdictStr Used       = "USED"
verdictStr Dead       = "DEAD"
verdictStr Unresolved = "UNRESOLVED"

-- any Used -> Used; else any Unresolved -> Unresolved; else Dead.
combine :: [V] -> V
combine vs
  | Used `elem` vs       = Used
  | Unresolved `elem` vs = Unresolved
  | otherwise            = Dead

-- ---- interface cache (keyed by .agdai path) ---------------------------------

type Cache = IORef (Map FilePath (Maybe Interface))

readIfaceCached :: Cache -> AbsolutePath -> TCM (Maybe Interface)
readIfaceCached cache apath = do
  let key = filePath apath
  m <- liftIO (readIORef cache)
  case Map.lookup key m of
    Just hit -> pure hit
    Nothing  -> do
      mfile <- liftIO (mkInterfaceFile apath)
      r <- maybe (pure Nothing) readInterface mfile
      liftIO (modifyIORef' cache (Map.insert key r))
      pure r

defsOf :: Interface -> HMap.HashMap QName Definition
defsOf iface = iSignature iface ^. sigDefinitions

usedOf :: Interface -> Set QName
usedOf iface = namesIn (toList (defsOf iface))

-- ---- scope resolution -------------------------------------------------------

scopeMap :: Interface -> Map String Scope
scopeMap iface =
  Map.fromList [ (prettyShow mn, sc) | (mn, sc) <- Map.toList (iInsideScope iface ^. scopeModules) ]

exportsOf :: Scope -> Map String [QName]
exportsOf sc = Map.fromListWith (++)
  [ (prettyShow cn, map anameName (List1.toList xs))
  | (cn, xs) <- Map.toList (allNamesInScope sc :: Map C.Name (List1 AbstractName)) ]

valueLookup :: Map String Scope -> String -> String -> [QName]
valueLookup scopes modS name = case Map.lookup modS scopes of
  Nothing -> []
  Just sc -> fromMaybe [] (Map.lookup name (exportsOf sc))

moduleExports :: Map String Scope -> String -> [QName]
moduleExports scopes key = case Map.lookup key scopes of
  Nothing -> []
  Just sc -> concat (Map.elems (exportsOf sc))

-- ---- copy -> origin bridge --------------------------------------------------

isFunctionCopy :: Definition -> Bool
isFunctionCopy d = defCopy d && case theDef d of { Function{} -> True; _ -> False }

-- The QName(s) a Function copy delegates to: the head of each clause body (peel
-- Lam; take the Def/Con head; drop elims = section args, and the type).
delegatedHeads :: Definition -> [QName]
delegatedHeads d = case theDef d of
  Function{funClauses = cls} -> concatMap clauseHead cls
  _                          -> []
  where
    clauseHead cl = maybe [] termHead (clauseBody cl)
    termHead (Def q _)   = [q]
    termHead (Con c _ _) = [conName c]
    termHead (Lam _ b)   = termHead (unAbs b)
    termHead _           = []

-- Read q's OWN defining interface and look it up.  The defining file is the
-- qnameModule with its submodule suffix stripped; the boundary is unmarked, so
-- strip-retry from the full module name down, taking the first prefix whose
-- interface both resolves AND contains q.
defOf :: Cache -> QName -> TCM (Maybe Definition)
defOf cache q = go (length parts)
  where
    parts = mnameToList (qnameModule q)
    go 0 = pure Nothing
    go n = do
      let raw = rawTopLevelModuleNameForModuleName (MName (take n parts))
      tlm   <- topLevelModuleName raw
      efile <- findFile' tlm
      case efile of
        Left _    -> go (n - 1)
        Right src -> do
          ipath  <- toIFile src
          miface <- readIfaceCached cache ipath
          case miface >>= HMap.lookup q . defsOf of
            Just d  -> pure (Just d)
            Nothing -> go (n - 1)

isUsedDeep :: Cache -> Set QName -> QName -> Set QName -> TCM V
isUsedDeep cache used q visited
  | q `Set.member` used    = pure Used
  | q `Set.member` visited = pure Dead
  | otherwise = do
      mdef <- defOf cache q
      case mdef of
        Nothing -> pure Unresolved
        Just d
          | isFunctionCopy d -> case delegatedHeads d of
              [] -> pure Unresolved
              hs -> combine <$> mapM (\h -> isUsedDeep cache used h (Set.insert q visited)) hs
          | otherwise -> pure Dead

resolveQuery :: Cache -> Set QName -> Map String Scope -> String -> String -> TCM V
resolveQuery cache used scopes modS name = do
  let qs = valueLookup scopes modS name ++ moduleExports scopes (modS ++ "." ++ name)
  if null qs then pure Unresolved
  else combine <$> mapM (\q -> isUsedDeep cache used q Set.empty) qs

-- ---- driver -----------------------------------------------------------------

data Query = Query { qAgdai :: FilePath, qMod :: String, qName :: String }

parseQuery :: String -> Maybe Query
parseQuery l = case splitTab l of
  (a : b : c : _) | not (null a) -> Just (Query a b c)
  _                              -> Nothing

main :: IO ()
main = do
  hSetEncoding stdout utf8
  incs  <- maybe [] (filter (not . null) . splitColon) <$> lookupEnv "AGDA_IWYU_INCLUDE_PATHS"
  input <- getContents
  let queries    = [ q | l <- lines input, Just q <- [parseQuery l] ]
      byConsumer = Map.toList (Map.fromListWith (++) [ (qAgdai q, [q]) | q <- queries ])
  cache <- newIORef Map.empty
  res <- runTCMTop $ do
    setCommandLineOptions defaultOptions { optIncludePaths = incs }
    forM byConsumer $ \(agdai, qs) -> do
      apath  <- liftIO (absolute agdai)
      miface <- readIfaceCached cache apath
      case miface of
        Nothing    -> pure [ errLine q "decode failed" | q <- qs ]
        Just iface -> do
          let used   = usedOf iface
              scopes = scopeMap iface
          forM qs $ \q -> do
            v <- resolveQuery cache used scopes (qMod q) (qName q)
            pure (verdictLine q v)
  case res of
    Left _   -> putStr ""   -- a top-level TCM error: emit nothing (driver treats absent as oracle)
    Right ls -> mapM_ putStrLn (concat ls)

verdictLine :: Query -> V -> String
verdictLine q v = jsonObj
  [ ("path", jsonStr (qAgdai q)), ("mod", jsonStr (qMod q))
  , ("name", jsonStr (qName q)), ("verdict", jsonStr (verdictStr v)) ]

errLine :: Query -> String -> String
errLine q msg = jsonObj
  [ ("path", jsonStr (qAgdai q)), ("mod", jsonStr (qMod q))
  , ("name", jsonStr (qName q)), ("error", jsonStr msg) ]

-- ---- tiny JSON encoder + splitters -----------------------------------------

jsonStr :: String -> String
jsonStr s = '"' : concatMap esc s ++ "\""
  where
    esc '"'  = "\\\""
    esc '\\' = "\\\\"
    esc '\n' = "\\n"
    esc '\r' = "\\r"
    esc '\t' = "\\t"
    esc c    = [c]

jsonObj :: [(String, String)] -> String
jsonObj kvs = "{" ++ intercalate "," [ jsonStr k ++ ":" ++ v | (k, v) <- kvs ] ++ "}"

splitColon :: String -> [String]
splitColon s = case break (== ':') s of
  (a, ':' : rest) -> a : splitColon rest
  (a, _)          -> [a]

splitTab :: String -> [String]
splitTab s = case break (== '\t') s of
  (a, '\t' : rest) -> a : splitTab rest
  (a, _)           -> [a]
