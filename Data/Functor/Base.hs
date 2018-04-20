{-# LANGUAGE CPP #-}

-- See Data.Functor.Foldable for explanation
#ifndef MIN_VERSION_transformers_compat
#define MIN_VERSION_transformers_compat(x,y,z) 0
#endif

#define EXPLICIT_DICT_FUNCTOR_CLASSES (MIN_VERSION_base(4,9,0) || MIN_VERSION_transformers(0,5,0) || (MIN_VERSION_transformers_compat(0,5,0) && !MIN_VERSION_transformers(0,4,0)))

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

import Data.Functor.Classes
  ( Eq1(..), Ord1(..), Show1(..), Read1(..)
#if EXPLICIT_DICT_FUNCTOR_CLASSES
  , Eq2(..), Ord2(..), Show2(..), Read2(..)
#endif
  )

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

#if EXPLICIT_DICT_FUNCTOR_CLASSES
instance Eq2 NonEmptyF where
  liftEq2 f g (NonEmptyF a mb) (NonEmptyF a' mb') = f a a' && liftEq g mb mb'

instance Eq a => Eq1 (NonEmptyF a) where
  liftEq = liftEq2 (==)

instance Ord2 NonEmptyF where
  liftCompare2 f g (NonEmptyF a mb) (NonEmptyF a' mb') = f a a' `mappend` liftCompare g mb mb'

instance Ord a => Ord1 (NonEmptyF a) where
  liftCompare = liftCompare2 compare

instance Show a => Show1 (NonEmptyF a) where
  liftShowsPrec = liftShowsPrec2 showsPrec showList

instance Show2 NonEmptyF where
  liftShowsPrec2 sa _ sb slb d (NonEmptyF a b) = showParen (d > 10)
    $ showString "NonEmptyF "
    . sa 11 a
    . showString " "
    . liftShowsPrec sb slb 11 b

instance Read2 NonEmptyF where
  liftReadsPrec2 ra _ rb rlb d = readParen (d > 10) $ \s -> cons s
    where
      cons s0 = do
        ("NonEmptyF", s1) <- lex s0
        (a,      s2) <- ra 11 s1
        (mb,     s3) <- liftReadsPrec rb rlb 11 s2
        return (NonEmptyF a mb, s3)

instance Read a => Read1 (NonEmptyF a) where
  liftReadsPrec = liftReadsPrec2 readsPrec readList

#else
instance Eq a   => Eq1   (NonEmptyF a) where eq1        = (==)
instance Ord a  => Ord1  (NonEmptyF a) where compare1   = compare
instance Show a => Show1 (NonEmptyF a) where showsPrec1 = showsPrec
instance Read a => Read1 (NonEmptyF a) where readsPrec1 = readsPrec
#endif

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
