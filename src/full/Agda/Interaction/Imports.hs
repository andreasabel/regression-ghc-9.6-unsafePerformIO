{-# LANGUAGE CPP #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE RecursiveDo #-}

{-# OPTIONS_GHC -Wall #-}

{-| This module deals with finding imported modules and loading their
    interface files.
-}
module Agda.Interaction.Imports
  ( typeCheckMain
  ) where

import Control.Monad.IO.Class (liftIO)


import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Common (underscore)
import Agda.Syntax.Position (noRange)
import Agda.Syntax.TopLevelModuleName
  ( TopLevelModuleName, unsafeTopLevelModuleName, rawTopLevelModuleNameForQName )
import Agda.Syntax.Translation.ConcreteToAbstract (concreteToAbstract_, TopLevel(..))

import Agda.TypeChecking.Monad (TCM, envCurrentPath, localTC)
import Agda.TypeChecking.Monad.Options ( setPragmaOptions )

import Agda.Interaction.Options.Base (defaultPragmaOptions, lensOptVerbose, parseVerboseKey)

import Agda.Utils.FileName (pattern AbsolutePath)
import Agda.Utils.Null (empty)
import Agda.Utils.Lens
import qualified Agda.Utils.Maybe.Strict as Strict
import qualified Agda.Utils.Trie as Trie

typeCheckMain :: TCM ()
typeCheckMain = do
  let srcPath = AbsolutePath "ImpossibleVerboseReduceM.agda"
  -- liftIO $ print srcPath

  localTC (\e -> e { envCurrentPath = Just srcPath }) $ do

    let verb = Strict.Just $ Trie.singleton (parseVerboseKey "impossible") 10
    setPragmaOptions $ set lensOptVerbose verb defaultPragmaOptions

    -- Scope checking.
    _topLevel <- do

      let msg = words "ReduceM SHOULD ALSO PRINT THIS DEBUG MESSAGE!!!!!!!!!!!!! LET'S MAKE IT VERY LONG SO IT CANNOT BE OVERLOOKED!!!!!!!!!!!!!!!!!!!"
      let ds = [C.Pragma $ C.ImpossiblePragma noRange msg]
      let topDecls = [C.Module noRange undefined underscore empty ds]

      let x = unsafeTopLevelModuleName (rawTopLevelModuleNameForQName underscore) undefined
      concreteToAbstract_ (TopLevel srcPath x topDecls)

    return ()
