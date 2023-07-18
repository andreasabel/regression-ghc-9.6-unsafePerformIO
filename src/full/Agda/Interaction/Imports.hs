{-# LANGUAGE CPP #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE RecursiveDo #-}

{-# OPTIONS_GHC -Wall #-}

{-| This module deals with finding imported modules and loading their
    interface files.
-}
module Agda.Interaction.Imports
  ( Source(..)
  , parseSource
  , typeCheckMain
  ) where

import qualified Data.Text.Lazy as TL

import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Parser (moduleParser, parseFile, readFilePM)
import Agda.Syntax.Position (mkRangeFile)
import Agda.Syntax.TopLevelModuleName (TopLevelModuleName)
import Agda.Syntax.Translation.ConcreteToAbstract (concreteToAbstract_, TopLevel(..))

import Agda.TypeChecking.Warnings (runPM)
import Agda.TypeChecking.Monad (TCM, envCurrentPath, localTC, setOptionsFromPragma)

import Agda.Interaction.FindFile (SourceFile(..), moduleName)
import Agda.Interaction.Library.Base (OptionsPragma(..))

-- | The decorated source code.

data Source = Source
  { srcOrigin      :: SourceFile            -- ^ Source location at the time of its parsing
  , srcModule      :: C.Module              -- ^ The parsed module.
  , srcModuleName  :: TopLevelModuleName    -- ^ The top-level module name.
  }

-- | Parses a source file and prepares the 'Source' record.

parseSource :: SourceFile -> TCM Source
parseSource sourceFile@(SourceFile f) = do
  (parsedMod, parsedModName) <- mdo
    -- This piece of code uses mdo because the top-level module name
    -- (parsedModName) is obtained from the parser's result, but it is
    -- also used by the parser.
    let rf = mkRangeFile f (Just parsedModName)
    source <- runPM $ readFilePM rf
    ((parsedMod, _attrs), _fileType)
      <- runPM $ parseFile moduleParser rf $ TL.unpack source
    parsedModName <- moduleName f parsedMod
    return (parsedMod, parsedModName)
  return Source
    { srcOrigin      = sourceFile
    , srcModule      = parsedMod
    , srcModuleName  = parsedModName
    }

srcFilePragmas :: Source -> [OptionsPragma]
srcFilePragmas src = pragmas
  where
  cpragmas = C.modPragmas (srcModule src)
  pragmas = [ OptionsPragma
                { pragmaStrings = opts
                , pragmaRange   = r
                }
            | C.OptionsPragma r opts <- cpragmas
            ]


typeCheckMain
  :: Source
     -- ^ The decorated source code.
  -> TCM ()
typeCheckMain src = do
  let srcPath = srcFilePath $ srcOrigin src

  localTC (\e -> e { envCurrentPath = Just srcPath }) $ do

    mapM_ setOptionsFromPragma (srcFilePragmas src)

    -- Scope checking.
    _topLevel <- do
      let topDecls = C.modDecls $ srcModule src
      concreteToAbstract_ (TopLevel srcPath (srcModuleName src) topDecls)

    return ()
