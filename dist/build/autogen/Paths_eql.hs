{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -fno-warn-implicit-prelude #-}
module Paths_eql (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/Users/david/.cabal/bin"
libdir     = "/Users/david/.cabal/lib/x86_64-osx-ghc-8.2.2/eql-0.1.0.0-G2xhYFPFnvWIfY6XtuDEQJ"
dynlibdir  = "/Users/david/.cabal/lib/x86_64-osx-ghc-8.2.2"
datadir    = "/Users/david/.cabal/share/x86_64-osx-ghc-8.2.2/eql-0.1.0.0"
libexecdir = "/Users/david/.cabal/libexec"
sysconfdir = "/Users/david/.cabal/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "eql_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "eql_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "eql_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "eql_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "eql_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "eql_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
