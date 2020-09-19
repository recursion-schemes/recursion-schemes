{-# LANGUAGE FlexibleInstances, FunctionalDependencies, GADTs, UndecidableInstances #-}
module RecursionSchemes.Custom.Gather where

import qualified Data.Functor.Foldable as F


type Gather base a pos
  = a -> base pos -> pos


class PosUntrans f where
  untransformed :: f pos -> pos

class Recur a pos | pos -> a where
  recur :: pos -> a

instance {-# OVERLAPPABLE #-} (PosUntrans f, Recur a pos) => Recur a (f pos) where
  recur = recur . untransformed


data RecFun t a where
  RecFun :: (Recur a pos, base ~ F.Base t)
         => (base pos -> pos)
         -> RecFun t a

runRecFun
  :: F.Recursive t
  => RecFun t a
  -> t -> a
runRecFun (RecFun f)
  = recur . F.cata f

recFun
  :: (Recur a pos, base ~ F.Base t)
  => Gather base a pos
  -> (base pos -> a)
  -> RecFun t a
recFun gather f
  = RecFun $ \ps -> gather (f ps) ps
