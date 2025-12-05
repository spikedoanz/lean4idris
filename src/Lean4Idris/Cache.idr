||| Global file-based caching for type checker results
|||
||| Cache is shared across all export files. Declarations are assumed to have
||| globally unique names (which is true in Lean). Cache is invalidated when
||| the type checker version changes.
module Lean4Idris.Cache

import Data.SortedSet
import Data.String
import Data.List
import System.File
import System.Directory
import System

%default total

||| Type checker version - change this when the type checker changes
||| to invalidate all caches
export
tcVersion : String
tcVersion = "lean4idris-v1"

||| Cache state tracking which declarations have passed
public export
record CacheState where
  constructor MkCacheState
  version : String
  passedDecls : SortedSet String

||| Create an empty cache
export
initCache : CacheState
initCache = MkCacheState tcVersion empty

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

||| Get the global cache file path
export
covering
getGlobalCachePath : IO String
getGlobalCachePath = do
  cacheDir <- getCacheDir
  pure (cacheDir ++ "/global.cache")

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
|||   VERSION <version>
|||   <decl1>
|||   <decl2>
|||   ...
parseCacheContent : String -> Maybe CacheState
parseCacheContent content =
  let ls = lines content
  in case ls of
    [] => Nothing
    (firstLine :: rest) =>
      case words firstLine of
        ["VERSION", v] =>
          if v == tcVersion
            then Just $ MkCacheState v (fromList rest)
            else Nothing  -- Version mismatch, cache invalid
        _ => Nothing  -- Invalid format

||| Serialize cache state to string
serializeCache : CacheState -> String
serializeCache st =
  let header = "VERSION " ++ st.version
      decls = Prelude.toList st.passedDecls
  in unlines (header :: decls)

||| Load global cache from disk if it exists and version matches
export
covering
loadCache : IO (Maybe CacheState)
loadCache = do
  cachePath <- getGlobalCachePath
  result <- readFile cachePath
  case result of
    Left _ => pure Nothing  -- File doesn't exist or can't be read
    Right content => pure (parseCacheContent content)

||| Save cache to disk
export
covering
saveCache : CacheState -> IO ()
saveCache st = do
  ok <- ensureCacheDir
  when ok $ do
    cachePath <- getGlobalCachePath
    let content = serializeCache st
    _ <- writeFile cachePath content
    pure ()
