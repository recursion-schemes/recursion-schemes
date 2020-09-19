module RecursionSchemes
  ( Base, ListF(..), Recursive(project), Corecursive(embed)

  , RecFun, runRecFun, recFun
  , Recur(..), CataPos, cata
  , Untouched(..), ParaPosT, paraT, para
  , Fast(..), ZygoPosT, withZygotizedRecFun, zygoT, zygo
  , Cofree, histoT, histo

  , CorecFun, runCorecFun, corecFun
  , Seed(..), AnaPos, ana
  , Done(..), ApoPosT, apoT, apo
  , Switch(..), GapoPosT, gapoT, gapo
  , Free, futuT, futu
  ) where

import Control.Comonad.Cofree
import Control.Monad.Free

import Data.Functor.Foldable hiding (cata, para, zygo, histo, ana, apo, gapo, futu)
import RecursionSchemes.Custom.Gather
import RecursionSchemes.Custom.Scatter
