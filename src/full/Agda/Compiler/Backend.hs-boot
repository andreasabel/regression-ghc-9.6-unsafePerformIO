
module Agda.Compiler.Backend
  ( Backend
  , lookupBackend
  )
  where

import Control.DeepSeq

import Agda.Syntax.Abstract.Name (QName)
import {-# SOURCE #-} Agda.TypeChecking.Monad.Base (TCM, BackendName)

data Backend

instance NFData Backend

lookupBackend :: BackendName -> TCM (Maybe Backend)
