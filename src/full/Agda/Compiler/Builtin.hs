{-|
  Built-in backends.
-}

module Agda.Compiler.Builtin where

import Agda.Compiler.Backend (Backend)

import Agda.Interaction.Highlighting.Dot (dotBackend)
import Agda.Interaction.Highlighting.HTML (htmlBackend)
import Agda.Interaction.Highlighting.LaTeX (latexBackend)

builtinBackends :: [Backend]
builtinBackends =
  [ dotBackend
  , htmlBackend
  , latexBackend
  ]
