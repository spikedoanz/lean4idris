||| Global file-based caching for type checker results
|||
||| Cache is shared across all export files. Declarations are assumed to have
||| globally unique names (which is true in Lean). Cache is invalidated when
||| the type checker version changes (passed in at runtime).
module Lean4Idris.Cache

import Data.SortedSet
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
  version : String
  passedDecls : SortedSet String

||| Create an empty cache with the given version
export
initCache : String -> CacheState
initCache version = MkCacheState version empty

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

||| Get the cache directory path (~/.cache/lean4idris/)
export
covering
getCacheDir : IO String
getCacheDir = do
  home <- getEnv "HOME"
  case home of
    Just h => pure (h ++ "/.cache/lean4idris")
    Nothing => pure "/tmp/lean4idris-cache"

||| Get the cache file path for a specific version
export
covering
getCachePath : String -> IO String
getCachePath version = do
  cacheDir <- getCacheDir
  pure (cacheDir ++ "/" ++ version ++ ".cache")

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

||| Parse cache file content, checking version matches expected
||| Format:
|||   VERSION <version>
|||   <decl1>
|||   <decl2>
|||   ...
parseCacheContent : String -> String -> Maybe CacheState
parseCacheContent expectedVersion content =
  let ls = lines content
  in case ls of
    [] => Nothing
    (firstLine :: rest) =>
      case words firstLine of
        ["VERSION", v] =>
          if v == expectedVersion
            then Just $ MkCacheState v (fromList rest)
            else Nothing  -- Version mismatch, cache invalid
        _ => Nothing  -- Invalid format

||| Serialize cache state to string
serializeCache : CacheState -> String
serializeCache st =
  let header = "VERSION " ++ st.version
      decls = Prelude.toList st.passedDecls
  in unlines (header :: decls)

||| Load cache from disk for a specific version
export
covering
loadCache : String -> IO (Maybe CacheState)
loadCache version = do
  cachePath <- getCachePath version
  result <- readFile cachePath
  case result of
    Left _ => pure Nothing  -- File doesn't exist or can't be read
    Right content => pure (parseCacheContent version content)

||| Save cache to disk (uses version from cache state)
export
covering
saveCache : CacheState -> IO ()
saveCache st = do
  ok <- ensureCacheDir
  when ok $ do
    cachePath <- getCachePath st.version
    let content = serializeCache st
    _ <- writeFile cachePath content
    pure ()
