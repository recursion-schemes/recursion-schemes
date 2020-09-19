module RecursionSchemes
  ( Base, ListF(..), Recursive(project), Corecursive(embed)
  , RecFun, runRecFun, recFun
  , Recur(..), CataPos, cata
  , Untouched(..), ParaPosT, paraT, para
  , Fast(..), ZygoPosT, withZygotizedRecFun, zygoT, zygo
  , Cofree, histoT, histo
  ) where

import Control.Comonad.Cofree
import Data.Functor.Foldable hiding (cata, para, zygo, histo)
import RecursionSchemes.Custom
