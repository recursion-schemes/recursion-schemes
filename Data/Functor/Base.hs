{-# LANGUAGE CPP #-}

#define HAS_GENERIC (__GLASGOW_HASKELL__ >= 702)
#define HAS_GENERIC1 (__GLASGOW_HASKELL__ >= 706)

#ifdef __GLASGOW_HASKELL__
{-# LANGUAGE DeriveDataTypeable #-}
#if HAS_GENERIC
{-# LANGUAGE DeriveGeneric #-}
#endif
#endif

-- | Base Functors for standard types not already expressed as a fixed point.
module Data.Functor.Base
  ( NonEmptyF(..)
  ) where

#ifdef __GLASGOW_HASKELL__
import Data.Data (Typeable)
#if HAS_GENERIC
import GHC.Generics (Generic)
#endif
#if HAS_GENERIC1
import GHC.Generics (Generic1)
#endif
#endif

import Control.Applicative
import Data.Monoid

import qualified Data.Foldable as F
import qualified Data.Traversable as T

import qualified Data.Bifunctor as Bi
import qualified Data.Bifoldable as Bi
import qualified Data.Bitraversable as Bi

import Prelude hiding (head, tail)

-- | Base Functor for 'Data.List.NonEmpty'
data NonEmptyF a b = NonEmptyF { head :: a, tail :: Maybe b }
  deriving (Eq,Ord,Show,Read,Typeable
#if HAS_GENERIC
          , Generic
#endif
#if HAS_GENERIC1
          , Generic1
#endif
          )

-- These instances cannot be auto-derived on with GHC <= 7.6
instance Functor (NonEmptyF a) where
  fmap f = NonEmptyF <$> head <*> (fmap f . tail)

instance F.Foldable (NonEmptyF a) where
  foldMap f = F.foldMap f . tail

instance T.Traversable (NonEmptyF a) where
  traverse f = fmap <$> (NonEmptyF . head) <*> (T.traverse f . tail)

instance Bi.Bifunctor NonEmptyF where
  bimap f g = NonEmptyF <$> (f . head) <*> (fmap g . tail)

instance Bi.Bifoldable NonEmptyF where
  bifoldMap f g = merge <$> (f . head) <*> (fmap g . tail)
    where merge x my = maybe x (mappend x) my

instance Bi.Bitraversable NonEmptyF where
  bitraverse f g = liftA2 NonEmptyF <$> (f . head) <*> (T.traverse g . tail)
