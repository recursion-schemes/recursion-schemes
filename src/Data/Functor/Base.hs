{-# LANGUAGE CPP #-}
#include "recursion-schemes-common.h"

#ifdef __GLASGOW_HASKELL__
{-# LANGUAGE DeriveDataTypeable #-}
#if HAS_GENERIC
{-# LANGUAGE DeriveGeneric #-}
#endif
#endif

-- | Base Functors for standard types not already expressed as a fixed point.
module Data.Functor.Base
  ( ListF (..)
  , NonEmptyF(..)
  , TreeF (..), ForestF,
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
#ifdef LIFTED_FUNCTOR_CLASSES
  , Eq2(..), Ord2(..), Show2(..), Read2(..)
#endif
  )

import qualified Data.Foldable as F
import qualified Data.Traversable as T

import qualified Data.Bifunctor as Bi
import qualified Data.Bifoldable as Bi
import qualified Data.Bitraversable as Bi

import Prelude hiding (head, tail)

-------------------------------------------------------------------------------
-- ListF
-------------------------------------------------------------------------------

-- | Base functor of @[]@.
data ListF a b = Nil | Cons a b
  deriving (Eq,Ord,Show,Read,Typeable
#if HAS_GENERIC
          , Generic
#endif
#if HAS_GENERIC1
          , Generic1
#endif
          )

#ifdef LIFTED_FUNCTOR_CLASSES
instance Eq2 ListF where
  liftEq2 _ _ Nil        Nil          = True
  liftEq2 f g (Cons a b) (Cons a' b') = f a a' && g b b'
  liftEq2 _ _ _          _            = False

instance Eq a => Eq1 (ListF a) where
  liftEq = liftEq2 (==)

instance Ord2 ListF where
  liftCompare2 _ _ Nil        Nil          = EQ
  liftCompare2 _ _ Nil        _            = LT
  liftCompare2 _ _ _          Nil          = GT
  liftCompare2 f g (Cons a b) (Cons a' b') = f a a' `mappend` g b b'

instance Ord a => Ord1 (ListF a) where
  liftCompare = liftCompare2 compare

instance Show a => Show1 (ListF a) where
  liftShowsPrec = liftShowsPrec2 showsPrec showList

instance Show2 ListF where
  liftShowsPrec2 _  _ _  _ _ Nil        = showString "Nil"
  liftShowsPrec2 sa _ sb _ d (Cons a b) = showParen (d > 10)
    $ showString "Cons "
    . sa 11 a
    . showString " "
    . sb 11 b

instance Read2 ListF where
  liftReadsPrec2 ra _ rb _ d = readParen (d > 10) $ \s -> nil s ++ cons s
    where
      nil s0 = do
        ("Nil", s1) <- lex s0
        return (Nil, s1)
      cons s0 = do
        ("Cons", s1) <- lex s0
        (a,      s2) <- ra 11 s1
        (b,      s3) <- rb 11 s2
        return (Cons a b, s3)

instance Read a => Read1 (ListF a) where
  liftReadsPrec = liftReadsPrec2 readsPrec readList

#else
instance Eq a   => Eq1   (ListF a) where eq1        = (==)
instance Ord a  => Ord1  (ListF a) where compare1   = compare
instance Show a => Show1 (ListF a) where showsPrec1 = showsPrec
instance Read a => Read1 (ListF a) where readsPrec1 = readsPrec
#endif

-- These instances cannot be auto-derived on with GHC <= 7.6
instance Functor (ListF a) where
  fmap _ Nil        = Nil
  fmap f (Cons a b) = Cons a (f b)

instance F.Foldable (ListF a) where
  foldMap _ Nil        = Data.Monoid.mempty
  foldMap f (Cons _ b) = f b

instance T.Traversable (ListF a) where
  traverse _ Nil        = pure Nil
  traverse f (Cons a b) = Cons a <$> f b

instance Bi.Bifunctor ListF where
  bimap _ _ Nil        = Nil
  bimap f g (Cons a b) = Cons (f a) (g b)

instance Bi.Bifoldable ListF where
  bifoldMap _ _ Nil        = mempty
  bifoldMap f g (Cons a b) = mappend (f a) (g b)

instance Bi.Bitraversable ListF where
  bitraverse _ _ Nil        = pure Nil
  bitraverse f g (Cons a b) = Cons <$> f a <*> g b

-------------------------------------------------------------------------------
-- NonEmpty
-------------------------------------------------------------------------------

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

#ifdef LIFTED_FUNCTOR_CLASSES
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

-------------------------------------------------------------------------------
-- Tree
-------------------------------------------------------------------------------

-- | Base functor for 'Data.Tree.Tree'.
data TreeF a b = NodeF a (ForestF a b)
  deriving (Eq,Ord,Show,Read,Typeable
#if HAS_GENERIC
          , Generic
#endif
#if HAS_GENERIC1
          , Generic1
#endif
          )

type ForestF a b = [b]

#ifdef LIFTED_FUNCTOR_CLASSES
instance Eq2 TreeF where
  liftEq2 f g (NodeF a mb) (NodeF a' mb') = f a a' && liftEq g mb mb'

instance Eq a => Eq1 (TreeF a) where
  liftEq = liftEq2 (==)

instance Ord2 TreeF where
  liftCompare2 f g (NodeF a mb) (NodeF a' mb') = f a a' `mappend` liftCompare g mb mb'

instance Ord a => Ord1 (TreeF a) where
  liftCompare = liftCompare2 compare

instance Show a => Show1 (TreeF a) where
  liftShowsPrec = liftShowsPrec2 showsPrec showList

instance Show2 TreeF where
  liftShowsPrec2 sa _ sb slb d (NodeF a b) = showParen (d > 10)
    $ showString "NodeF "
    . sa 11 a
    . showString " "
    . liftShowsPrec sb slb 11 b

instance Read2 TreeF where
  liftReadsPrec2 ra _ rb rlb d = readParen (d > 10) $ \s -> cons s
    where
      cons s0 = do
        ("NodeF", s1) <- lex s0
        (a,      s2) <- ra 11 s1
        (mb,     s3) <- liftReadsPrec rb rlb 11 s2
        return (NodeF a mb, s3)

instance Read a => Read1 (TreeF a) where
  liftReadsPrec = liftReadsPrec2 readsPrec readList

#else
instance Eq a   => Eq1   (TreeF a) where eq1        = (==)
instance Ord a  => Ord1  (TreeF a) where compare1   = compare
instance Show a => Show1 (TreeF a) where showsPrec1 = showsPrec
instance Read a => Read1 (TreeF a) where readsPrec1 = readsPrec
#endif

-- These instances cannot be auto-derived on with GHC <= 7.6
instance Functor (TreeF a) where
  fmap f (NodeF x xs) = NodeF x (fmap f xs)

instance F.Foldable (TreeF a) where
  foldMap f (NodeF _ xs) = F.foldMap f xs

instance T.Traversable (TreeF a) where
  traverse f (NodeF x xs) = NodeF x <$> T.traverse f xs

instance Bi.Bifunctor TreeF where
  bimap f g (NodeF x xs) = NodeF (f x) (fmap g xs)

instance Bi.Bifoldable TreeF where
  bifoldMap f g (NodeF x xs) = f x `mappend` F.foldMap g xs

instance Bi.Bitraversable TreeF where
  bitraverse f g (NodeF x xs) = liftA2 NodeF (f x) (T.traverse g xs)
