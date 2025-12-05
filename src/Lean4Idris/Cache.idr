||| Simple file-based caching for type checker results
module Lean4Idris.Cache

import Data.SortedSet
import Data.SortedMap
import Data.String
import Data.List
import System.File
import System.Directory
import System

%default total

||| Cache state tracking which declarations have passed
public export
record CacheState where
  constructor MkCacheState
  exportHash : String
  passedDecls : SortedSet String

||| Create an empty cache with the given export hash
export
initCache : String -> CacheState
initCache h = MkCacheState h empty

||| Check if a declaration is in the cache
export
isCached : String -> CacheState -> Bool
isCached name st = contains name st.passedDecls

||| Add a passed declaration to the cache
export
addPassed : String -> CacheState -> CacheState
addPassed name st = { passedDecls $= insert name } st

||| Get number of cached declarations
export
cacheSize : CacheState -> Nat
cacheSize st = length (Prelude.toList st.passedDecls)

||| Simple string hash (FNV-1a variant)
||| Good distribution, fast, no dependencies
export
covering
simpleHash : String -> String
simpleHash s =
  let fnvOffset : Integer = 2166136261
      fnvPrime : Integer = 16777619
      modVal : Integer = 4294967296  -- 2^32
      bytes = unpack s
      hash = foldl (\h, c => ((h `mod` modVal) * fnvPrime + cast (ord c)) `mod` modVal) fnvOffset bytes
  in show hash

||| Get the cache directory path (~/.cache/lean4idris/)
export
covering
getCacheDir : IO String
getCacheDir = do
  home <- getEnv "HOME"
  case home of
    Just h => pure (h ++ "/.cache/lean4idris")
    Nothing => pure "/tmp/lean4idris-cache"

||| Get the cache file path for a given export file
export
covering
getCachePath : String -> IO String
getCachePath exportPath = do
  cacheDir <- getCacheDir
  let pathHash = simpleHash exportPath
  pure (cacheDir ++ "/" ++ pathHash ++ ".cache")

||| Ensure the cache directory exists
export
covering
ensureCacheDir : IO Bool
ensureCacheDir = do
  cacheDir <- getCacheDir
  result <- createDir cacheDir
  case result of
    Right () => pure True
    Left FileExists => pure True
    Left _ => pure False

||| Parse cache file content
||| Format:
|||   HASH <hash>
|||   <decl1>
|||   <decl2>
|||   ...
parseCacheContent : String -> String -> Maybe CacheState
parseCacheContent expectedHash content =
  let ls = lines content
  in case ls of
    [] => Nothing
    (firstLine :: rest) =>
      case words firstLine of
        ["HASH", h] =>
          if h == expectedHash
            then Just $ MkCacheState h (fromList rest)
            else Nothing  -- Hash mismatch, cache invalid
        _ => Nothing  -- Invalid format

||| Serialize cache state to string
serializeCache : CacheState -> String
serializeCache st =
  let header = "HASH " ++ st.exportHash
      decls = Prelude.toList st.passedDecls
  in unlines (header :: decls)

||| Load cache from disk if it exists and hash matches
export
covering
loadCache : (exportPath : String) -> (exportHash : String) -> IO (Maybe CacheState)
loadCache exportPath exportHash = do
  cachePath <- getCachePath exportPath
  result <- readFile cachePath
  case result of
    Left _ => pure Nothing  -- File doesn't exist or can't be read
    Right content => pure (parseCacheContent exportHash content)

||| Save cache to disk
export
covering
saveCache : (exportPath : String) -> CacheState -> IO ()
saveCache exportPath st = do
  ok <- ensureCacheDir
  when ok $ do
    cachePath <- getCachePath exportPath
    let content = serializeCache st
    _ <- writeFile cachePath content
    pure ()
