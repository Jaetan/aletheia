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
-- tools/agda-iwyu-reader/test/): a candidate is USED iff ANY of three signals,
-- all read from the .agdai, fires for a QName it resolves to in scope:
--   (1) SEMANTIC -- the QName is in `namesIn (iSignature)` (the elaborated
--       terms): direct defs, re-exports, datatype/constructor copies, and the
--       instance / implicit / literal-backed uses source highlighting misses.
--   (2) SYNTACTIC -- its definition site is referenced by a source token, by
--       OCCURRENCE COUNT from `iHighlighting`.  An import-listed name always
--       contributes one occurrence (the `using (...)` token), so a VALUE needs
--       count >= 2 to be a body use; a MODULE MEMBER is not import-listed, so any
--       occurrence (>= 1) is a use.  This catches PATTERN SYNONYMS, which expand
--       to constructors and so never reach the signature.
--   (3) DELEGATED -- a module-application Function COPY whose delegated origin
--       reaches the used-set.  A copy's body is `Def origin <section-args>`; we
--       take the clause-body HEAD (dropping the type and args, which would leak
--       unrelated QNames -- the false-"used" trap) and recurse.  def q is read
--       from q's OWN defining interface, auto-derived from its qnameModule (the
--       file boundary is unmarked, so strip-retry the module-name prefix until
--       one resolves AND contains q), cached by path.
-- DEAD means none of the three fired (every real use mechanism is covered, so
-- this is the no-false-negative guarantee).  UNRESOLVED is reserved for a
-- candidate that cannot be resolved in scope at all (should not happen for a
-- real candidate); the driver routes it to the recompile-confirm oracle, never
-- to DEAD.
--
-- Include paths (project src + stdlib src) come from $AGDA_IWYU_INCLUDE_PATHS
-- (colon-separated); they MUST match what wrote the interfaces.
module Main (main) where

import           Control.Monad (filterM, forM)
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
import           Agda.Syntax.Abstract.Name (ModuleName (..), QName, nameBindingSite, qnameModule, qnameName)
import           Agda.Syntax.Common.Aspect (Aspects (..), DefinitionSite (..))
import           Agda.Syntax.Common.Pretty (prettyShow)
import qualified Agda.Syntax.Concrete.Name as C
import           Agda.Syntax.Internal (Abs (..), Clause (..), ConHead (..), Term (..))
import           Agda.Syntax.Internal.Names (namesIn)
import           Agda.Syntax.Position (posPos, rStart, rangeFileName, srcFile)
import           Agda.Syntax.Scope.Base (AbstractName (..), Scope, allNamesInScope, scopeModules)
import           Agda.Syntax.TopLevelModuleName (rawTopLevelModuleNameForModuleName)
import           Agda.TypeChecking.Monad.Base
                   (Definition, Interface, TCM, defCopy, funClauses, iHighlighting, iInsideScope,
                    iSignature, pattern Function, runTCMTop, sigDefinitions, theDef)
import           Agda.TypeChecking.Monad.Options (setCommandLineOptions)
import           Agda.TypeChecking.Monad.State (topLevelModuleName)
import           Agda.Utils.FileName (AbsolutePath, absolute, filePath)
import           Agda.Utils.Lens ((^.))
import           Agda.Utils.List1 (List1)
import qualified Agda.Utils.List1 as List1
import qualified Agda.Utils.Maybe.Strict as Strict
import qualified Agda.Utils.RangeMap as RangeMap

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

-- The SYNTACTIC use signal: how many source tokens reference each definition
-- site, keyed by (defining-module, position).  This is the complement of the
-- semantic `usedOf` set -- it captures source-level uses that elaboration
-- erases, notably PATTERN SYNONYMS (which expand to constructors, so never
-- appear in the signature).  An import-listed name always contributes one
-- occurrence (the `using (...)` token itself), so a *value* candidate is used
-- in the body iff its count is >= 2; a *module member* is not in the import
-- list, so any occurrence (>= 1) is a real use.
highlightCount :: Interface -> Map (String, Int) Int
highlightCount iface = Map.fromListWith (+)
  [ ((prettyShow (defSiteModule ds), defSitePos ds), 1)
  | (_, asp) <- RangeMap.toList (iHighlighting iface)
  , Just ds  <- [definitionSite asp] ]

-- A QName's own definition site as (module, position), to look up its count.
defKey :: QName -> Maybe (String, Int)
defKey q = do
  pos  <- rStart (nameBindingSite (qnameName q))
  rf   <- Strict.toLazy (srcFile pos)
  modn <- rangeFileName rf
  pure (prettyShow modn, fromIntegral (posPos pos))

-- Number of source tokens referencing q's definition (0 if its site is unknown).
occurrences :: Map (String, Int) Int -> QName -> Int
occurrences hc q = maybe 0 (\k -> Map.findWithDefault 0 k hc) (defKey q)

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

-- Semantic + delegated-copy verdict for one scope QName.  The syntactic signal
-- is added by the caller; here defOf failure (pattern synonym / not in any
-- signature) or a non-copy not in `used` means no semantic use => Dead.
semDeep :: Cache -> Set QName -> QName -> Set QName -> TCM V
semDeep cache used q visited
  | q `Set.member` used    = pure Used
  | q `Set.member` visited = pure Dead
  | otherwise = do
      mdef <- defOf cache q
      case mdef of
        Nothing -> pure Dead
        Just d
          | isFunctionCopy d -> combine <$> mapM (\h -> semDeep cache used h (Set.insert q visited)) (delegatedHeads d)
          | otherwise        -> pure Dead

-- ASSUMPTION (load-bearing for FN-safety): a value candidate is listed in
-- exactly ONE `using`/`renaming` clause, contributing exactly one highlight
-- occurrence, so a body use means count >= 2.  This holds for the dead-import
-- gate (every candidate is import-listed).  When NARROWING lands (Step 3), a
-- wildcard `open import M` contributes ZERO import tokens, so the threshold must
-- generalize to `importOccurrences(candidate) + 1` (the driver, which parses the
-- opens, supplies that count) -- otherwise a used-once syntactic-only name from a
-- wildcard open would count 1 < 2 and be a FALSE NEGATIVE.
resolveQuery :: Cache -> Set QName -> Map (String, Int) Int -> Map String Scope -> String -> String -> TCM V
resolveQuery cache used hc scopes modS name = do
  let valQs = valueLookup scopes modS name                  -- import-listed: a body use needs count >= 2
      modQs = moduleExports scopes (modS ++ "." ++ name)     -- members: any occurrence (>= 1) is a use
      qs    = valQs ++ modQs
      synUsed = any (\q -> occurrences hc q >= 2) valQs
             || any (\q -> occurrences hc q >= 1) modQs
  if null qs        then pure Unresolved  -- not in scope at all (should not happen for a real candidate)
  else if synUsed   then pure Used        -- syntactic: referenced in the source beyond its import
  else combine <$> mapM (\q -> semDeep cache used q Set.empty) qs


anyM :: (Monad m) => (a -> m Bool) -> [a] -> m Bool
anyM p = foldr (\x acc -> p x >>= \b -> if b then pure True else acc) (pure False)


-- The USED subset of a WILDCARD `open import M`'s exports: each export concrete
-- name kept iff some QName it resolves to is used.  A wildcard contributes NO
-- import-list token, so the syntactic threshold is 1 (any occurrence is a body
-- use) — cf. the value query's threshold 2.  This is what narrowing replaces the
-- wildcard with; the driver judges DEAD (empty) / REDUNDANT (subset of the
-- explicit imports) / NARROWABLE from it.
resolveWildcard :: Cache -> Set QName -> Map (String, Int) Int -> Map String Scope -> String -> TCM [String]
resolveWildcard cache used hc scopes modS = case Map.lookup modS scopes of
  Nothing -> pure []
  Just sc -> map fst <$> filterM memberUsed (Map.toList (exportsOf sc))
  where
    memberUsed (_, qs)
      | any (\q -> occurrences hc q >= 1) qs = pure True
      | otherwise = anyM (\q -> (== Used) <$> semDeep cache used q Set.empty) qs

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
              hc     = highlightCount iface
              scopes = scopeMap iface
          forM qs $ \q ->
            if qName q == "*"
              then wildcardLine q <$> resolveWildcard cache used hc scopes (qMod q)
              else verdictLine q <$> resolveQuery cache used hc scopes (qMod q) (qName q)
  case res of
    Left _   -> putStr ""   -- a top-level TCM error: emit nothing (driver treats absent as oracle)
    Right ls -> mapM_ putStrLn (concat ls)

verdictLine :: Query -> V -> String
verdictLine q v = jsonObj
  [ ("path", jsonStr (qAgdai q)), ("mod", jsonStr (qMod q))
  , ("name", jsonStr (qName q)), ("verdict", jsonStr (verdictStr v)) ]

-- A wildcard query (`mod *`) reports the USED subset of M's exports instead of a
-- single verdict, for the driver's narrowing / redundancy decision.
wildcardLine :: Query -> [String] -> String
wildcardLine q names = jsonObj
  [ ("path", jsonStr (qAgdai q)), ("mod", jsonStr (qMod q))
  , ("name", jsonStr "*"), ("used", jsonArr (map jsonStr names)) ]

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

jsonArr :: [String] -> String
jsonArr xs = "[" ++ intercalate "," xs ++ "]"

splitColon :: String -> [String]
splitColon s = case break (== ':') s of
  (a, ':' : rest) -> a : splitColon rest
  (a, _)          -> [a]

splitTab :: String -> [String]
splitTab s = case break (== '\t') s of
  (a, '\t' : rest) -> a : splitTab rest
  (a, _)           -> [a]
