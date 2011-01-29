{-# OPTIONS_GHC -fglasgow-exts #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Recursion.Cata
-- Copyright   :  (C) 2008 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable (rank-2 polymorphism)
-- 
----------------------------------------------------------------------------
module Data.Recursion.Cata 
  ( cata, g_cata, distCata
  ) where

import Data.Functor.Extend
import Control.Category.Hask
import Control.Functor
import Control.Functor.Pointed
import Control.Functor.Algebra 
import Control.Functor.Extras
import Control.Functor.Fix
import Control.Functor.HigherOrder
import Control.Functor.KanExtension
import Control.Functor.KanExtension.Interpreter
import Control.Monad.Identity

-- | 
-- 
-- > cata f = g_cata distCata (liftAlgebra f)
cata :: Functor f => (f a -> a) -> Mu f -> a
cata f = f . fmap (cata f) . outF

-- | 
--
-- > g_cata k f = g_hylo k distAna f id outM
gcata :: (Functor f, Extend w) => Dist f w -> (f (w a) -> a) -> Mu f -> a
gcata k g = extract . c where c = fmap g . k . fmap (duplicate . c) . outF

-- | 
--
-- > distCata 
distCata :: Functor f => Dist f Identity
distCata = Identity . fmap runIdentity

-- | Mendler style catamorphism.
mcata :: (forall a. (a -> c) -> f a -> c) -> Mu f -> c 
mcata phi = phi (mcata phi) . outF   
