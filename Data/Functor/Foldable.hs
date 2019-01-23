{-# LANGUAGE CPP, TypeFamilies, Rank2Types, FlexibleContexts, FlexibleInstances, GADTs, StandaloneDeriving, UndecidableInstances #-}
#include "recursion-schemes-common.h"

#ifdef __GLASGOW_HASKELL__
{-# LANGUAGE DeriveDataTypeable #-}
#if __GLASGOW_HASKELL__ >= 800
{-# LANGUAGE ConstrainedClassMethods #-}
#endif
#if HAS_GENERIC
{-# LANGUAGE DeriveGeneric #-}
#endif
#endif

-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2008-2015 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
----------------------------------------------------------------------------
module Data.Functor.Foldable
  (
  -- * Base functors for fixed points
    Base
  , ListF(..)
  -- * Fixed points
  , Fix(..), unfix
  , Mu(..), hoistMu
  , Nu(..), hoistNu
  -- * Folding
  , Recursive(..)
  -- ** Combinators
  , gcata
  , zygo
  , gzygo
  , histo
  , ghisto
  -- ** Distributive laws
  , distCata
  , distPara
  , distParaT
  , distZygo
  , distZygoT
  , distHisto
  , distGHisto
  -- * Unfolding
  , Corecursive(..)
  -- ** Combinators
  , gapo
  , gana
  , futu
  , gfutu
  -- ** Distributive laws
  , distAna
  , distApo
  , distGApo
  , distGApoT
  , distFutu
  , distGFutu
  -- * Refolding
  , hylo
  , ghylo
  , chrono
  , gchrono
  -- ** Changing representation
  , hoist
  , refix
  -- * Common names
  , fold, gfold
  , unfold, gunfold
  , refold, grefold
  -- * Mendler-style
  , mcata
  , mhisto
  -- * Elgot (co)algebras
  , elgot
  , coelgot
  -- * Zygohistomorphic prepromorphisms
  , zygoHistoPrepro
  -- * Effectful combinators
  , cataA
  , transverse
  ) where

import Control.Applicative
import Control.Comonad
import Control.Comonad.Trans.Class
import Control.Comonad.Trans.Env
import qualified Control.Comonad.Cofree as Cofree
import Control.Comonad.Cofree (Cofree(..))
import           Control.Comonad.Trans.Cofree (CofreeF, CofreeT(..))
import qualified Control.Comonad.Trans.Cofree as CCTC
import Control.Monad (liftM, join)
import Control.Monad.Free (Free(..))
import qualified Control.Monad.Free.Church as CMFC
import Control.Monad.Trans.Except (ExceptT(..), runExceptT)
import           Control.Monad.Trans.Free (FreeF, FreeT(..))
import qualified Control.Monad.Trans.Free as CMTF
import Data.Functor.Identity
import Control.Arrow
import Data.Function (on)
import Data.Functor.Classes
import Data.Functor.Compose (Compose(..))
import Data.List.NonEmpty(NonEmpty((:|)), nonEmpty, toList)
import Text.Read
import Text.Show
#ifdef __GLASGOW_HASKELL__
import Data.Data hiding (gunfold)
#if HAS_POLY_TYPEABLE
#else
import qualified Data.Data as Data
#endif
#if HAS_GENERIC
import GHC.Generics (Generic)
#endif
#if HAS_GENERIC1
import GHC.Generics (Generic1)
#endif
#endif
import Numeric.Natural
import Data.Monoid (Monoid (..))
import Prelude

import qualified Data.Foldable as F
import qualified Data.Traversable as T

import qualified Data.Bifunctor as Bi
import qualified Data.Bifoldable as Bi
import qualified Data.Bitraversable as Bi

import           Data.Functor.Base hiding (head, tail)
import qualified Data.Functor.Base as NEF (NonEmptyF(..))

-- | Obtain the base functor for a recursive datatype.
--
-- The core idea of this library is that instead of writing recursive functions
-- on a recursive datatype, we prefer to write non-recursive functions on a
-- related, non-recursive datatype we call the "base functor".
--
-- For example, @[a]@ is a recursive type, and its corresponding base functor is
-- @ListF a@:
--
-- > data ListF a b = Nil | Cons a b
-- > type instance Base [a] = ListF a
--
-- The relationship between those two types is that if we replace @b@ with
-- @ListF a@, we obtain a type which is isomorphic to @[a]@.
type family Base t :: * -> *

-- | A recursive datatype which can be unrolled one recursion layer at a time.
--
-- For example, a value of type @[a]@ can be unrolled into a @ListF a [a]@. If
-- that unrolled value is a 'Cons', it contains another @[a]@ which can be
-- unrolled as well, and so on.
--
-- Typically, 'Recursive' types also have a 'Corecursive' instance, in which
-- case 'project' and 'embed' are inverses.
class Functor (Base t) => Recursive t where
  -- | Unroll a single recursion layer.
  --
  -- >>> project [1,2,3]
  -- Cons 1 [2,3]
  project :: t -> Base t t

  -- | A generalization of 'foldr'. The elements of the base functor, called the
  -- "recursive positions", give the result of folding the sub-tree at that
  -- position.
  --
  -- > -- |
  -- > -- >>> sum [1,2,3]
  -- > -- 6
  -- > sum :: [Int] -> Int
  -- > sum = cata sumF
  -- >
  -- > sumF :: ListF Int Int -> Int
  -- > sumF Nil          = 0
  -- > sumF (Cons x acc) = x + acc
  cata :: (Base t a -> a) -- ^ a (Base t)-algebra
       -> t               -- ^ fixed point
       -> a               -- ^ result
  cata f = c where c = f . fmap c . project

  -- | A variant of 'cata' in which recursive positions also include the
  -- original sub-tree, in addition to the result of folding that sub-tree.
  --
  -- Useful when matching on a pattern which spans more than one recursion step:
  --
  -- > -- |
  -- > -- >>> splitAtCommaSpace "one, two, three"
  -- > -- Just ("one","two, three")
  -- > splitAtCommaSpace :: String -> Maybe (String,String)
  -- > splitAtCommaSpace = para splitAtCommaSpaceF
  -- >
  -- > splitAtCommaSpaceF :: ListF Char (String, Maybe (String,String))
  -- >                    -> Maybe (String,String)
  -- > splitAtCommaSpaceF (Cons ',' (' ':ys, _))     = Just ([], ys)
  -- > splitAtCommaSpaceF (Cons x (_, Just (xs,ys))) = Just (x:xs, ys)
  -- > splitAtCommaSpaceF _                          = Nothing
  para :: (Base t (t, a) -> a) -> t -> a
  para t = p where p x = t . fmap ((,) <*> p) $ project x

  -- | A generalized paramorphism. Like 'para', each recursive position gives
  -- the result of the fold on its sub-tree and also the sub-tree itself.
  -- Depending on the distributive law, more information about that sub-tree may
  -- also be provided.
  --
  -- For example, we could build a "zygomorphic paramorphism", in which the
  -- result of a 'cata' is also provided:
  --
  -- > -- |
  -- > -- >>> calc "subtract 2; multiply by 2; add 1" <*> pure 42
  -- > -- Just 81
  -- > calc :: String -> Maybe (Int -> Int)
  -- > calc = gpara (distZygo parseNumberF) calcF
  -- >
  -- > parseDigit :: Char -> Maybe Int
  -- > parseDigit c = (ord c - ord '0') <$ guard (c `elem` ['0'..'9'])
  -- >
  -- > parseNumberF :: ListF Char (Maybe Int) -> Maybe Int
  -- > parseNumberF Nil              = Nothing
  -- > parseNumberF (Cons ';' _)     = Nothing
  -- > parseNumberF (Cons c Nothing) = parseDigit c
  -- > parseNumberF (Cons c maybeY)
  -- >   | c `elem` ['0'..'9'] = (\x y -> 10 * x + y) <$> parseDigit c <*> maybeY
  -- >   | otherwise           = maybeY
  -- >
  -- > calcF :: ListF Char (EnvT String
  -- >                           ((,) (Maybe Int))
  -- >                           (Maybe (Int -> Int)))
  -- >       -> Maybe (Int -> Int)
  -- > calcF Nil = Just id
  -- > calcF (Cons c (EnvT cs (maybeX,maybeF)))
  -- >   | "add "         `isPrefixOf` (c:cs) = (\f x -> f . (+ x))        <$> maybeF <*> maybeX
  -- >   | "subtract "    `isPrefixOf` (c:cs) = (\f x -> f . (subtract x)) <$> maybeF <*> maybeX
  -- >   | "multiply by " `isPrefixOf` (c:cs) = (\f x -> f . (* x))        <$> maybeF <*> maybeX
  -- >   | otherwise                          = maybeF
  gpara :: (Corecursive t, Comonad w) => (forall b. Base t (w b) -> w (Base t b)) -> (Base t (EnvT t w a) -> a) -> t -> a
  gpara t = gzygo embed t

  -- | Fokkinga's prepromorphism. Applies the natural transformation /n/ times
  -- to the base functors at depth /n/, then collapses the results using a
  -- 'cata'. The outermost base functor has depth zero.
  --
  -- Useful for indenting sub-trees in a pretty-printer:
  --
  -- > -- |
  -- > -- >>> putStr $ drawList ["foo","bar","baz"]
  -- > -- foo
  -- > --   bar
  -- > --     baz
  -- > drawList :: [String] -> String
  -- > drawList = prepro indent drawListF
  -- >
  -- > indent :: ListF String a -> ListF String a
  -- > indent Nil        = Nil
  -- > indent (Cons s x) = Cons ("  " ++ s) x
  -- >
  -- > drawListF :: ListF String String -> String
  -- > drawListF Nil               = ""
  -- > drawListF (Cons line lines) = line ++ "\n" ++ lines
  prepro
    :: Corecursive t
    => (forall b. Base t b -> Base t b)
    -> (Base t a -> a)
    -> t
    -> a
  prepro e f = c where c = f . fmap (c . hoist e) . project

  -- | A generalized prepromorphism. Like 'prepro', the natural transformation
  -- is applied /n/ times to the base functors at depth /n/. The results are
  -- then folded using the operation corresponding to the given distributive
  -- law.
  --
  -- For example, we could build a "zygomorphic prepromorphism", which folds the
  -- results using a 'zygo':
  --
  -- > type Tree a = Fix (TreeF a)
  -- > data TreeF a b = Leaf a | Branch b b
  -- >   deriving Functor
  -- >
  -- > leaf :: a -> Tree a
  -- > leaf = Fix . Leaf
  -- >
  -- > branch :: Tree a -> Tree a -> Tree a
  -- > branch l r = Fix $ Branch l r
  -- >
  -- > -- |
  -- > -- >>> let tree = ((leaf "0.1.1.1" `branch` leaf "0.1.1.2") `branch` leaf "0.1.2") `branch` (leaf "0.2.1" `branch` leaf "0.2.2")
  -- > -- >>> putStrLn $ drawTree tree
  -- > -- 0.
  -- > --   0.1.
  -- > --     0.1.1.
  -- > --       0.1.1.1
  -- > --       0.1.1.2
  -- > --     0.1.2
  -- > --   0.2.
  -- > --     0.2.1
  -- > --     0.2.2
  -- > drawTree :: Tree String -> String
  -- > drawTree = gprepro (distZygo mergeHeaders) indent drawTreeF
  -- >
  -- > indent :: TreeF String a -> TreeF String a
  -- > indent (Leaf s) = Leaf ("  " ++ s)
  -- > indent x        = x
  -- >
  -- > mergeHeaders :: TreeF String String -> String
  -- > mergeHeaders (Leaf s) = s
  -- > mergeHeaders (Branch s1 s2)
  -- >   = drop 2
  -- >   $ takeWhile (/= '\0')
  -- >   $ zipWith (\c1 c2 -> if c1 == c2 then c1 else '\0') s1 s2
  -- >
  -- > drawTreeF :: TreeF String (String, String) -> String
  -- > drawTreeF (Leaf s) = s
  -- > drawTreeF (Branch (header1, s1) (header2, s2))
  -- >   = mergeHeaders (Branch header1 header2) ++ "\n"
  -- >  ++ s1 ++ "\n"
  -- >  ++ s2
  gprepro
    :: (Corecursive t, Comonad w)
    => (forall b. Base t (w b) -> w (Base t b))
    -> (forall c. Base t c -> Base t c)
    -> (Base t (w a) -> a)
    -> t
    -> a
  gprepro k e f = extract . c where c = fmap f . k . fmap (duplicate . c . hoist e) . project

distPara :: Corecursive t => Base t (t, a) -> (t, Base t a)
distPara = distZygo embed

distParaT :: (Corecursive t, Comonad w) => (forall b. Base t (w b) -> w (Base t b)) -> Base t (EnvT t w a) -> EnvT t w (Base t a)
distParaT t = distZygoT embed t

-- | A recursive datatype which can be rolled up one recursion layer at a time.
--
-- For example, a value of type @ListF a [a]@ can be rolled up into a @[a]@.
-- This @[a]@ can then be used in a 'Cons' to construct another @List F a [a]@,
-- which can be rolled up as well, and so on.
--
-- Typically, 'Corecursive' types also have a 'Recursive' instance, in which
-- case 'embed' and 'project' are inverses.
class Functor (Base t) => Corecursive t where
  -- | Roll up a single recursion layer.
  --
  -- >>> embed (Cons 1 [2,3])
  -- [1,2,3]
  embed :: Base t t -> t

  -- | A generalization of 'unfoldr'. The starting seed is expanded into a base
  -- functor whose recursive positions contain more seeds, which are themselves
  -- expanded, and so on.
  --
  -- > -- |
  -- > -- >>> enumFromTo 1 4
  -- > -- [1,2,3,4]
  -- > enumFromTo :: Int -> Int -> [Int]
  -- > enumFromTo lo hi = ana go lo where
  -- >   go :: Int -> ListF Int Int
  -- >   go i = if i > hi then Nil else Cons i (i+1)
  ana
    :: (a -> Base t a) -- ^ a (Base t)-coalgebra
    -> a               -- ^ seed
    -> t               -- ^ resulting fixed point
  ana g = a where a = embed . fmap a . g

  -- | A variant of 'ana' in which recursive positions may contain a sub-tree
  -- instead of a seed.
  --
  -- Useful for short-circuiting the remainder of the unfolding:
  --
  -- > -- |
  -- > -- >>> mergeSortedLists [1,4,6,9] [2,4,6,7,10]
  -- > -- [1,2,4,4,6,6,7,9,10]
  -- > mergeSortedLists :: [Int] -> [Int] -> [Int]
  -- > mergeSortedLists xs1 xs2 = apo mergeSortedListsF (xs1,xs2)
  -- >
  -- > mergeSortedListsF :: ([Int],[Int]) -> ListF Int (Either [Int] ([Int],[Int]))
  -- > mergeSortedListsF ([], []) = Nil
  -- > mergeSortedListsF ([], x:xs2) = Cons x $ Left xs2
  -- > mergeSortedListsF (x:xs1, []) = Cons x $ Left xs1
  -- > mergeSortedListsF (x1:xs1, x2:xs2)
  -- >   | x1 <= x2  = Cons x1 $ Right (xs1, x2:xs2)
  -- >   | otherwise = Cons x2 $ Right (x1:xs1, xs2)
  apo :: (a -> Base t (Either t a)) -> a -> t
  apo g = a where a = embed . (fmap (either id a)) . g

  -- | Fokkinga's postpromorphism. Uses an 'ana' on the seed, and then applies
  -- the natural transformation /n/ times to the base functors produced at depth
  -- /n/. The outermost base functor has depth zero.
  --
  -- > -- |
  -- > -- >>> take 8 $ iterate (*2) 1
  -- > -- [1,2,4,8,16,32,64,128]
  -- > iterate :: (Int -> Int) -> Int -> [Int]
  -- > iterate f = postpro apply go where
  -- >   apply :: ListF Int b -> ListF Int b
  -- >   apply Nil        = Nil
  -- >   apply (Cons x y) = Cons (f x) y
  -- >
  -- >   go :: Int -> ListF Int Int
  -- >   go x = Cons x x
  postpro
    :: Recursive t
    => (forall b. Base t b -> Base t b) -- natural transformation
    -> (a -> Base t a)                  -- a (Base t)-coalgebra
    -> a                                -- seed
    -> t
  postpro e g = a where a = embed . fmap (hoist e . a) . g

  -- | A generalized postpromorphism. The seed is expanded using the operation
  -- corresponding to the given distributive law, and then like in 'postpro',
  -- the natural transformation is applied /n/ times to the base functors at
  -- depth /n/.
  --
  -- For example, we could expand the seed using a 'gapo':
  --
  -- > -- |
  -- > -- >>> upThenFork 4
  -- > -- [(1,1),(2,2),(3,3),(4,4),(5,3),(6,2),(7,1)]
  -- > upThenFork :: Int -> [(Int,Int)]
  -- > upThenFork n = gpostpro (distGApo down) incrementFst up 1 where
  -- >   incrementFst :: ListF (Int,b) c -> ListF (Int,b) c
  -- >   incrementFst Nil             = Nil
  -- >   incrementFst (Cons (x, y) z) = Cons (1+x, y) z
  -- >
  -- >   up :: Int -> ListF (Int,Int) (Either Int Int)
  -- >   up i = Cons (1,i) (if i == n then Left (n-1) else Right (i+1))
  -- >
  -- >   down :: Int -> ListF (Int,Int) Int
  -- >   down 0 = Nil
  -- >   down i = Cons (1,i) (i-1)
  gpostpro
    :: (Recursive t, Monad m)
    => (forall b. m (Base t b) -> Base t (m b)) -- distributive law
    -> (forall c. Base t c -> Base t c)         -- natural transformation
    -> (a -> Base t (m a))                      -- a (Base t)-m-coalgebra
    -> a                                        -- seed
    -> t
  gpostpro k e g = a . return where a = embed . fmap (hoist e . a . join) . k . liftM g

-- | An optimized version of @cata f . ana g@.
--
-- Useful when your recursion structure is shaped like a particular recursive
-- datatype, but you're neither consuming nor producing that recursive datatype.
-- For example, the recursion structure of merge sort is a binary tree, but its
-- input and output is a list, not a binary tree.
--
-- > -- |
-- > -- >>> sort [1,5,2,8,4,9,8]
-- > -- [1,2,4,5,8,8,9]
-- > sort :: [Int] -> [Int]
-- > sort = hylo merge split where
-- >   split :: [Int] -> TreeF Int [Int]
-- >   split [x] = Leaf x
-- >   split xs  = uncurry Branch $ splitAt (length xs `div` 2) xs
-- >
-- >   merge :: TreeF Int [Int] -> [Int]
-- >   merge (Leaf x)         = [x]
-- >   merge (Branch xs1 xs2) = mergeSortedLists xs1 xs2
hylo :: Functor f => (f b -> b) -> (a -> f a) -> a -> b
hylo f g = h where h = f . fmap h . g

-- | A friendlier name for 'cata'.
fold :: Recursive t => (Base t a -> a) -> t -> a
fold = cata

-- | A friendlier name for 'ana'.
unfold :: Corecursive t => (a -> Base t a) -> a -> t
unfold = ana

-- | A friendlier name for 'hylo'.
refold :: Functor f => (f b -> b) -> (a -> f a) -> a -> b
refold = hylo

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

type instance Base [a] = ListF a
instance Recursive [a] where
  project (x:xs) = Cons x xs
  project [] = Nil

  para f (x:xs) = f (Cons x (xs, para f xs))
  para f [] = f Nil

instance Corecursive [a] where
  embed (Cons x xs) = x:xs
  embed Nil = []

  apo f a = case f a of
    Cons x (Left xs) -> x : xs
    Cons x (Right b) -> x : apo f b
    Nil -> []

type instance Base (NonEmpty a) = NonEmptyF a
instance Recursive (NonEmpty a) where
  project (x:|xs) = NonEmptyF x $ nonEmpty xs
instance Corecursive (NonEmpty a) where
  embed = (:|) <$> NEF.head <*> (maybe [] toList <$> NEF.tail)

type instance Base Natural = Maybe
instance Recursive Natural where
  project 0 = Nothing
  project n = Just (n - 1)
instance Corecursive Natural where
  embed = maybe 0 (+1)

-- | Cofree comonads are Recursive/Corecursive
type instance Base (Cofree f a) = CofreeF f a
instance Functor f => Recursive (Cofree f a) where
  project (x :< xs) = x CCTC.:< xs
instance Functor f => Corecursive (Cofree f a) where
  embed (x CCTC.:< xs) = x :< xs

-- | Cofree tranformations of comonads are Recursive/Corecusive
type instance Base (CofreeT f w a) = Compose w (CofreeF f a)
instance (Functor w, Functor f) => Recursive (CofreeT f w a) where
  project = Compose . runCofreeT
instance (Functor w, Functor f) => Corecursive (CofreeT f w a) where
  embed = CofreeT . getCompose

-- | Free monads are Recursive/Corecursive
type instance Base (Free f a) = FreeF f a

instance Functor f => Recursive (Free f a) where
  project (Pure a) = CMTF.Pure a
  project (Free f) = CMTF.Free f

improveF :: Functor f => CMFC.F f a -> Free f a
improveF x = CMFC.improve (CMFC.fromF x)
-- | It may be better to work with the instance for `CMFC.F` directly.
instance Functor f => Corecursive (Free f a) where
  embed (CMTF.Pure a) = Pure a
  embed (CMTF.Free f) = Free f
  ana               coalg = improveF . ana               coalg
  postpro       nat coalg = improveF . postpro       nat coalg
  gpostpro dist nat coalg = improveF . gpostpro dist nat coalg

-- | Free transformations of monads are Recursive/Corecursive
type instance Base (FreeT f m a) = Compose m (FreeF f a)
instance (Functor m, Functor f) => Recursive (FreeT f m a) where
  project = Compose . runFreeT
instance (Functor m, Functor f) => Corecursive (FreeT f m a) where
  embed = FreeT . getCompose

-- If you are looking for instances for the free MonadPlus, please use the
-- instance for FreeT f [].

-- If you are looking for instances for the free alternative and free
-- applicative, I'm sorry to disapoint you but you won't find them in this
-- package.  They can be considered recurive, but using non-uniform recursion;
-- this package only implements uniformly recursive folds / unfolds.

-- | Example boring stub for non-recursive data types
type instance Base (Maybe a) = Const (Maybe a)
instance Recursive (Maybe a) where project = Const
instance Corecursive (Maybe a) where embed = getConst

-- | Example boring stub for non-recursive data types
type instance Base (Either a b) = Const (Either a b)
instance Recursive (Either a b) where project = Const
instance Corecursive (Either a b) where embed = getConst

-- | A generalized catamorphism. With the appropriate distributive law, it can
-- be specialized to any fold: a 'cata', a 'para', a 'zygo', etc.
--
-- For example, we could build a version of 'zygo' in which the sub-trees are
-- folded with a 'para' instead of a 'cata':
--
-- > -- |
-- > -- >>> splitInThree "one, two, three, four"
-- > -- Just ("one","two","three, four")
-- > splitInThree :: String -> Maybe (String,String,String)
-- > splitInThree = gcata (dist splitAtCommaSpaceF) splitInThreeF
-- >
-- > splitInThreeF :: ListF Char ( (String, Maybe (String,String))
-- >                             , Maybe (String,String,String)
-- >                             )
-- >               -> Maybe (String,String,String)
-- > splitInThreeF (Cons ',' ((_, Just (' ':ys,zs)), _)) = Just ([], ys, zs)
-- > splitInThreeF (Cons x (_, Just (xs,ys,zs)))         = Just (x:xs, ys, zs)
-- > splitInThreeF _                                     = Nothing
-- >
-- > dist :: Corecursive t
-- >      => (Base t (t,b) -> b)
-- >      -> Base t ((t,b), a)
-- >      -> ((t,b), Base t a)
-- > dist f baseTBA = let baseTB = fst <$> baseTBA
-- >                      baseT  = fst <$> baseTB
-- >                      baseA  = snd <$> baseTBA
-- >                      b      = f baseTB
-- >                      t      = embed baseT
-- >                  in ((t,b), baseA)
gfold, gcata
  :: (Recursive t, Comonad w)
  => (forall b. Base t (w b) -> w (Base t b)) -- ^ a distributive law
  -> (Base t (w a) -> a)                      -- ^ a (Base t)-w-algebra
  -> t                                        -- ^ fixed point
  -> a
gcata k g = g . extract . c where
  c = k . fmap (duplicate . fmap g . c) . project
gfold k g t = gcata k g t

distCata :: Functor f => f (Identity a) -> Identity (f a)
distCata = Identity . fmap runIdentity

-- | A generalized anamorphism. With the appropriate distributive law, it can be
-- specialized to any unfold: an 'ana', an 'apo', a 'futu', etc.
--
-- For example, we could build a version of 'gapo' with three phases instead of
-- two:
--
-- > -- |
-- > -- >>> upDownUp 4
-- > -- [1,2,3,4,3,2,1,2,3,4]
-- > upDownUp :: Int -> [Int]
-- > upDownUp n = gana (dist upAgain down) up 1 where
-- >   up :: Int -> ListF Int (Int `Either` Int `Either` Int)
-- >   up i = Cons i (if i == n then Left (Right (n-1)) else Right (i+1))
-- >
-- >   down :: Int -> ListF Int (Either Int Int)
-- >   down i = Cons i (if i == 1 then Left 2 else Right (i-1))
-- >
-- >   upAgain :: Int -> ListF Int Int
-- >   upAgain i = if i > n then Nil else Cons i (i+1)
-- >
-- > dist :: Functor f
-- >      => (c -> f c)
-- >      -> (b -> f (Either c b))
-- >      -> c `Either` b `Either` f a
-- >      -> f (c `Either` b `Either` a)
-- > dist f _ (Left (Left z))  = Left <$> Left <$> f z
-- > dist _ g (Left (Right y)) = Left <$> g y
-- > dist _ _ (Right fx)       = Right <$> fx
gunfold, gana
  :: (Corecursive t, Monad m)
  => (forall b. m (Base t b) -> Base t (m b)) -- ^ a distributive law
  -> (a -> Base t (m a))                      -- ^ a (Base t)-m-coalgebra
  -> a                                        -- ^ seed
  -> t
gana k f = a . return . f where
  a = embed . fmap (a . liftM f . join) . k
gunfold k f t = gana k f t

distAna :: Functor f => Identity (f a) -> f (Identity a)
distAna = fmap Identity . runIdentity

-- | A generalized hylomorphism. Like a 'hylo', this is an optimized version of
-- an unfold followed by a fold. The fold and unfold operations correspond to
-- the given distributive laws.
--
-- For example, one way to implement @fib n@ is to compute @fib 1@ up to
-- @fib n@. This is a simple linear recursive structure which we can model by
-- unfolding our seed /n/ into a @Fix Maybe@ containing /n/ 'Just's. To do that,
-- a 'cata' is sufficient. We then fold the sub-tree containing /i/ 'Just's by
-- computing @fib i@ out of @fib (i-1)@ and @fib (i-2)@, the results of folding
-- two smaller sub-trees. To see more than one such result, we need a 'histo'.
--
-- > -- |
-- > -- >>> fmap fib [0..8]
-- > -- [1,1,2,3,5,8,13,21,34]
-- > fib :: Int -> Integer
-- > fib = ghylo distHisto distAna addF down where
-- >   down :: Int -> Maybe (Identity Int)
-- >   down 0 = Nothing
-- >   down n = Just (Identity (n-1))
-- >
-- >   addF :: Maybe (Cofree Maybe Integer) -> Integer
-- >   addF Nothing                     = 1
-- >   addF (Just (_ :< Nothing))       = 1
-- >   addF (Just (x :< Just (y :< _))) = x + y
grefold, ghylo
  :: (Comonad w, Functor f, Monad m)
  => (forall c. f (w c) -> w (f c))
  -> (forall d. m (f d) -> f (m d))
  -> (f (w b) -> b)
  -> (a -> f (m a))
  -> a
  -> b
ghylo w m f g = extract . h . return where
  h = fmap f . w . fmap (duplicate . h . join) . m . liftM g
grefold w m f g a = ghylo w m f g a

-- | A variant of 'ana' in which more than one recursive layer can be generated
-- before returning the next seed.
--
-- Useful for inserting a group of elements all at once:
--
-- > -- |
-- > -- >>> spaceOutCommas "foo,bar,baz"
-- > -- "foo, bar, baz"
-- > spaceOutCommas :: String -> String
-- > spaceOutCommas = futu go where
-- >   go :: String -> ListF Char (Free (ListF Char) String)
-- >   go []       = Nil
-- >   go (',':xs) = Cons ',' (Free (Cons ' ' (Pure xs)))
-- >   go (x:xs)   = Cons x (Pure xs)
futu :: Corecursive t => (a -> Base t (Free (Base t) a)) -> a -> t
futu = gana distFutu

gfutu :: (Corecursive t, Functor m, Monad m) => (forall b. m (Base t b) -> Base t (m b)) -> (a -> Base t (FreeT (Base t) m a)) -> a -> t
gfutu g = gana (distGFutu g)

distFutu :: Functor f => Free f (f a) -> f (Free f a)
distFutu (Pure fx) = Pure <$> fx
distFutu (Free ff) = Free . distFutu <$> ff

distGFutu :: (Functor f, Functor h) => (forall b. h (f b) -> f (h b)) -> FreeT f h (f a) -> f (FreeT f h a)
distGFutu k = d where
  d = fmap FreeT . k . fmap d' . runFreeT
  d' (CMTF.Pure ff) = CMTF.Pure <$> ff
  d' (CMTF.Free ff) = CMTF.Free . d <$> ff

-------------------------------------------------------------------------------
-- Fix
-------------------------------------------------------------------------------

-- | Construct a recursive datatype from a base functor.
--
-- For example, @[String]@ and @Fix (ListF String)@ are isomorphic:
--
-- > ["foo", "bar"]
-- > Fix (Cons "foo" (Fix (Cons "bar" (Fix Nil))))
--
-- Unlike 'Mu' and 'Nu', this representation is concrete, so we can
-- pattern-match on the constructors of @f@.
newtype Fix f = Fix (f (Fix f))

unfix :: Fix f -> f (Fix f)
unfix (Fix f) = f

instance Eq1 f => Eq (Fix f) where
  Fix a == Fix b = eq1 a b

instance Ord1 f => Ord (Fix f) where
  compare (Fix a) (Fix b) = compare1 a b

instance Show1 f => Show (Fix f) where
  showsPrec d (Fix a) =
    showParen (d >= 11)
      $ showString "Fix "
      . showsPrec1 11 a

instance Read1 f => Read (Fix f) where
  readPrec = parens $ prec 10 $ do
    Ident "Fix" <- lexP
    Fix <$> step (readS_to_Prec readsPrec1)

#ifdef __GLASGOW_HASKELL__
#if HAS_POLY_TYPEABLE
deriving instance Typeable Fix
deriving instance (Typeable f, Data (f (Fix f))) => Data (Fix f)
#else
instance Typeable1 f => Typeable (Fix f) where
   typeOf t = mkTyConApp fixTyCon [typeOf1 (undefined `asArgsTypeOf` t)]
     where asArgsTypeOf :: f a -> Fix f -> f a
           asArgsTypeOf = const

fixTyCon :: TyCon
#if MIN_VERSION_base(4,4,0)
fixTyCon = mkTyCon3 "recursion-schemes" "Data.Functor.Foldable" "Fix"
#else
fixTyCon = mkTyCon "Data.Functor.Foldable.Fix"
#endif
{-# NOINLINE fixTyCon #-}

instance (Typeable1 f, Data (f (Fix f))) => Data (Fix f) where
  gfoldl f z (Fix a) = z Fix `f` a
  toConstr _ = fixConstr
  gunfold k z c = case constrIndex c of
    1 -> k (z (Fix))
    _ -> error "gunfold"
  dataTypeOf _ = fixDataType

fixConstr :: Constr
fixConstr = mkConstr fixDataType "Fix" [] Prefix

fixDataType :: DataType
fixDataType = mkDataType "Data.Functor.Foldable.Fix" [fixConstr]
#endif
#endif

type instance Base (Fix f) = f
instance Functor f => Recursive (Fix f) where
  project (Fix a) = a
instance Functor f => Corecursive (Fix f) where
  embed = Fix

hoist :: (Recursive s, Corecursive t)
      => (forall a. Base s a -> Base t a) -> s -> t
hoist n = cata (embed . n)

-- |
-- >>> refix ["foo", "bar"] :: Fix (ListF String)
-- Fix (Cons "foo" (Fix (Cons "bar" (Fix Nil))))
refix :: (Recursive s, Corecursive t, Base s ~ Base t) => s -> t
refix = cata embed

toFix :: Recursive t => t -> Fix (Base t)
toFix = refix

fromFix :: Corecursive t => Fix (Base t) -> t
fromFix = refix


-------------------------------------------------------------------------------
-- Lambek
-------------------------------------------------------------------------------

-- | Lambek's lemma provides a default definition for 'project' in terms of 'cata' and 'embed'
lambek :: (Recursive t, Corecursive t) => (t -> Base t t)
lambek = cata (fmap embed)

-- | The dual of Lambek's lemma, provides a default definition for 'embed' in terms of 'ana' and 'project'
colambek :: (Recursive t, Corecursive t) => (Base t t -> t)
colambek = ana (fmap project)

-- |
-- The least fixed point of 'f', in the sense that if we did not have general
-- recursion, we would be forced to use the @f a -> a@ argument a finite number
-- of times and so we could only construct finite values. Since we do have
-- general recursion, 'Fix', 'Mu' and 'Nu' are all equivalent.
--
-- For example, @Fix (ListF String)@ and @Mu (ListF String)@ are isomorphic:
--
-- > Fix         (Cons "foo" (Fix (Cons "bar" (Fix Nil))))
-- > Mu (\f -> f (Cons "foo" (f   (Cons "bar" (f   Nil)))))
newtype Mu f = Mu (forall a. (f a -> a) -> a)
type instance Base (Mu f) = f
instance Functor f => Recursive (Mu f) where
  project = lambek
  cata f (Mu g) = g f
instance Functor f => Corecursive (Mu f) where
  embed m = Mu (\f -> f (fmap (fold f) m))

instance (Functor f, Eq1 f) => Eq (Mu f) where
  (==) = (==) `on` toFix

instance (Functor f, Ord1 f) => Ord (Mu f) where
  compare = compare `on` toFix

instance (Functor f, Show1 f) => Show (Mu f) where
  showsPrec d f = showParen (d > 10) $
    showString "fromFix " . showsPrec 11 (toFix f)

#ifdef __GLASGOW_HASKELL__
instance (Functor f, Read1 f) => Read (Mu f) where
  readPrec = parens $ prec 10 $ do
    Ident "fromFix" <- lexP
    fromFix <$> step readPrec
#endif

-- | A specialized, faster version of 'hoist' for 'Mu'.
hoistMu :: (forall a. f a -> g a) -> Mu f -> Mu g
hoistMu n (Mu mk) = Mu $ \roll -> mk (roll . n)


-- | Church encoded free monads are Recursive/Corecursive, in the same way that
-- 'Mu' is.
type instance Base (CMFC.F f a) = FreeF f a
cmfcCata :: (a -> r) -> (f r -> r) -> CMFC.F f a -> r
cmfcCata p f (CMFC.F run) = run p f
instance Functor f => Recursive (CMFC.F f a) where
  project = lambek
  cata f = cmfcCata (f . CMTF.Pure) (f . CMTF.Free)
instance Functor f => Corecursive (CMFC.F f a) where
  embed (CMTF.Pure a)  = CMFC.F $ \p _ -> p a
  embed (CMTF.Free fr) = CMFC.F $ \p f -> f $ fmap (cmfcCata p f) fr


-- |
-- The greatest fixed point of 'f', in the sense that even if we did not have
-- general recursion, we could still describe an infinite list by defining an
-- @a -> ListF Int a@ function which always returns a 'Cons'. Since we do have
-- general recursion, 'Fix', 'Mu' and 'Nu' are all equivalent.
--
-- For example, @Fix (ListF String)@ and @Nu (ListF String)@ are isomorphic:
--
-- > Fix            (Cons "foo" (Fix   (Cons "bar" (Fix    Nil))))
-- > Nu (\case {0 -> Cons "foo" 1; 1 -> Cons "bar" 2; _ -> Nil}) 0
data Nu f where Nu :: (a -> f a) -> a -> Nu f
type instance Base (Nu f) = f
instance Functor f => Corecursive (Nu f) where
  embed = colambek
  ana = Nu
instance Functor f => Recursive (Nu f) where
  project (Nu f a) = Nu f <$> f a

instance (Functor f, Eq1 f) => Eq (Nu f) where
  (==) = (==) `on` toFix

instance (Functor f, Ord1 f) => Ord (Nu f) where
  compare = compare `on` toFix

instance (Functor f, Show1 f) => Show (Nu f) where
  showsPrec d f = showParen (d > 10) $
    showString "fromFix " . showsPrec 11 (toFix f)

#ifdef __GLASGOW_HASKELL__
instance (Functor f, Read1 f) => Read (Nu f) where
  readPrec = parens $ prec 10 $ do
    Ident "fromFix" <- lexP
    fromFix <$> step readPrec
#endif

-- | A specialized, faster version of 'hoist' for 'Nu'.
hoistNu :: (forall a. f a -> g a) -> Nu f -> Nu g
hoistNu n (Nu next seed) = Nu (n . next) seed


-- | A variant of 'para' in which instead of also giving the original sub-tree,
-- the recursive positions give the result of applying a 'cata' to that
-- sub-tree. Thanks to the shared structure, 'zygo' is more efficient than
-- manually applying 'cata' inside a 'para'.
--
-- > -- | A variant of 'nub' which keeps the last occurrence instead of the first.
-- > --
-- > -- >>> nub [1,2,2,3,2,1,1,4]
-- > -- [1,2,3,4]
-- > -- >>> nubEnd [1,2,2,3,2,1,1,4]
-- > -- [3,2,1,4]
-- > nubEnd :: [Int] -> [Int]
-- > nubEnd = zygo gather go where
-- >   gather :: ListF Int (Set Int) -> Set Int
-- >   gather Nil         = Set.empty
-- >   gather (Cons x xs) = Set.insert x xs
-- >
-- >   go :: ListF Int (Set Int, [Int]) -> [Int]
-- >   go Nil                = []
-- >   go (Cons x (seen,xs)) = if Set.member x seen then xs else x:xs
zygo :: Recursive t => (Base t b -> b) -> (Base t (b, a) -> a) -> t -> a
zygo f = gfold (distZygo f)

distZygo
  :: Functor f
  => (f b -> b)             -- An f-algebra
  -> (f (b, a) -> (b, f a)) -- ^ A distributive for semi-mutual recursion
distZygo g m = (g (fmap fst m), fmap snd m)

-- | A generalized zygomorphism. Like 'zygo', each recursive position gives the
-- result of the fold on its sub-tree and also the result of a 'cata' on that
-- sub-tree. Depending on the distributive law, more information about that
-- sub-tree may also be provided.
--
-- For example, we could build a "zygomorphic zygomorphism", in which the result
-- of a second 'cata' is also provided:
--
-- > -- | Is any path from a node to a leaf more than twice as long as the path from
-- > -- that node to another leaf?
-- > --
-- > -- >>> take 10 $ map isUnbalanced $ iterate (\t -> leaf () `branch` t) $ leaf ()
-- > -- [False,False,False,False,True,True,True,True,True,True]
-- > isUnbalanced :: Tree a -> Bool
-- > isUnbalanced = gzygo minDepthF (distZygo maxDepthF) isUnbalancedF
-- >
-- > minDepthF :: TreeF a Int -> Int
-- > minDepthF (Leaf _)     = 1
-- > minDepthF (Branch x y) = 1 + min x y
-- >
-- > maxDepthF :: TreeF a Int -> Int
-- > maxDepthF (Leaf _)     = 1
-- > maxDepthF (Branch x y) = 1 + max x y
-- >
-- > isUnbalancedF :: TreeF a (EnvT Int ((,) Int) Bool) -> Bool
-- > isUnbalancedF (Leaf _) = False
-- > isUnbalancedF (Branch (EnvT min1 (max1, unbalanced1))
-- >                       (EnvT min2 (max2, unbalanced2)))
-- >   = unbalanced1 || unbalanced2 || 2 * (1 + min min1 min2) < (1 + max max1 max2)
gzygo
  :: (Recursive t, Comonad w)
  => (Base t b -> b)
  -> (forall c. Base t (w c) -> w (Base t c))
  -> (Base t (EnvT b w a) -> a)
  -> t
  -> a
gzygo f w = gfold (distZygoT f w)

distZygoT
  :: (Functor f, Comonad w)
  => (f b -> b)                        -- An f-w-algebra to use for semi-mutual recursion
  -> (forall c. f (w c) -> w (f c))    -- A base Distributive law
  -> f (EnvT b w a) -> EnvT b w (f a)  -- A new distributive law that adds semi-mutual recursion
distZygoT g k fe = EnvT (g (getEnv <$> fe)) (k (lower <$> fe))
  where getEnv (EnvT e _) = e

-- | A variant of 'apo' in which the short-circuiting sub-tree is described
-- using an 'ana'.
--
-- > -- |
-- > -- >>> upThenDown 4
-- > -- [1,2,3,4,3,2,1]
-- > upThenDown :: Int -> [Int]
-- > upThenDown n = gapo down up 1 where
-- >   up :: Int -> ListF Int (Either Int Int)
-- >   up i = Cons i (if i == n then Left (n-1) else Right (i+1))
-- >
-- >   down :: Int -> ListF Int Int
-- >   down 0 = Nil
-- >   down i = Cons i (i-1)
gapo :: Corecursive t => (b -> Base t b) -> (a -> Base t (Either b a)) -> a -> t
gapo g = gunfold (distGApo g)

distApo :: Recursive t => Either t (Base t a) -> Base t (Either t a)
distApo = distGApo project

distGApo :: Functor f => (b -> f b) -> Either b (f a) -> f (Either b a)
distGApo f = either (fmap Left . f) (fmap Right)

distGApoT
  :: (Functor f, Functor m)
  => (b -> f b)
  -> (forall c. m (f c) -> f (m c))
  -> ExceptT b m (f a)
  -> f (ExceptT b m a)
distGApoT g k = fmap ExceptT . k . fmap (distGApo g) . runExceptT

-- | Course-of-value iteration. Similar to 'para' in that each recursive position
-- also includes a representation of its original sub-tree in addition to the
-- result of folding that sub-tree, except that representation also includes the
-- results of folding the sub-trees of that sub-tree, as well as the results of
-- their sub-trees, etc.
--
-- Useful for folding more than one layer at a time:
--
-- > -- |
-- > -- >>> pairs [1,2,3,4]
-- > -- Just [(1,2),(3,4)]
-- > -- >>> pairs [1,2,3,4,5]
-- > -- Nothing
-- > pairs :: [Int] -> Maybe [(Int,Int)]
-- > pairs = histo pairsF
-- >
-- > pairsF :: ListF Int (Cofree (ListF Int) (Maybe [(Int,Int)]))
-- >        -> Maybe [(Int,Int)]
-- > pairsF Nil                                    = Just []
-- > pairsF (Cons x (_ :< Cons y (Just xys :< _))) = Just ((x,y):xys)
-- > pairsF _                                      = Nothing
histo :: Recursive t => (Base t (Cofree (Base t) a) -> a) -> t -> a
histo = gcata distHisto

ghisto :: (Recursive t, Comonad w) => (forall b. Base t (w b) -> w (Base t b)) -> (Base t (CofreeT (Base t) w a) -> a) -> t -> a
ghisto g = gcata (distGHisto g)

distHisto :: Functor f => f (Cofree f a) -> Cofree f (f a)
distHisto fc = fmap extract fc :< fmap (distHisto . Cofree.unwrap) fc

distGHisto :: (Functor f, Functor h) => (forall b. f (h b) -> h (f b)) -> f (CofreeT f h a) -> CofreeT f h (f a)
distGHisto k = d where d = CofreeT . fmap (\fc -> fmap CCTC.headF fc CCTC.:< fmap (d . CCTC.tailF) fc) . k . fmap runCofreeT

-- | An optimized version of a 'futu' followed by a 'histo'.
--
-- > -- |
-- > -- >>> putStr $ decompressImage [(1,'.'),(1,'*'),(3,'.'),(4,'*')]
-- > -- .*.
-- > -- ..*
-- > -- ***
-- > decompressImage :: [(Int,Char)] -> String
-- > decompressImage = chrono linesOf3 decodeRLE where
-- >   decodeRLE :: [(Int,Char)] -> ListF Char (Free (ListF Char) [(Int,Char)])
-- >   decodeRLE []          = Nil
-- >   decodeRLE ((n,c):ncs) = Cons c $ do
-- >     replicateM_ (n-1) $ Free $ Cons c $ Pure ()
-- >     pure ncs
-- >
-- >   linesOf3 :: ListF Char (Cofree (ListF Char) String) -> String
-- >   linesOf3 (Cons c1 (_ :< Cons c2 (_ :< Cons c3 (cs :< _)))) = c1:c2:c3:'\n':cs
-- >   linesOf3 _                                                 = ""
chrono :: Functor f => (f (Cofree f b) -> b) -> (a -> f (Free f a)) -> (a -> b)
chrono = ghylo distHisto distFutu

-- | An optimized version of a 'gfutu' followed by a 'ghisto'.
--
-- > -- |
-- > -- >>> putStr $ decompressImage [1,1,3,4]
-- > -- .*.
-- > -- ..*
-- > -- ***
-- > decompressImage :: [Int] -> String
-- > decompressImage = gchrono (distZygo toggle) distAna linesOf3 decodeRLE where
-- >   decodeRLE :: [Int] -> ListF Bool (Free (ListF Bool) [Int])
-- >   decodeRLE [] = Nil
-- >   decodeRLE (1:ns) = Cons True $ pure ns
-- >   decodeRLE (n:ns) = Cons False $ do
-- >     replicateM_ (n-2) $ writeBool False
-- >     writeBool True
-- >     pure ns
-- >
-- >   toggle :: ListF Bool Char -> Char
-- >   toggle Nil              = '.'
-- >   toggle (Cons False c)   = c
-- >   toggle (Cons True '.')  = '*'
-- >   toggle (Cons True _)    = '.'
-- >
-- >   linesOf3 :: ListF Bool (CofreeT (ListF Bool) ((,) Char) String) -> String
-- >   linesOf3 (Cons b1 (CofreeT (c2, _ :< Cons _
-- >                     (CofreeT (c3, _ :< Cons _
-- >                     (CofreeT (_,  s :< _)))))))
-- >     = toggle (Cons b1 c2) : c2 : c3 : '\n' : s
-- >   linesOf3 _ = ""
-- >
-- >   writeBool :: Bool -> Free (ListF Bool) ()
-- >   writeBool b = FreeT $ Identity $ Free $ Cons b $ pure ()
gchrono :: (Functor f, Functor w, Functor m, Comonad w, Monad m) =>
           (forall c. f (w c) -> w (f c)) ->
           (forall c. m (f c) -> f (m c)) ->
           (f (CofreeT f w b) -> b) -> (a -> f (FreeT f m a)) ->
           (a -> b)
gchrono w m = ghylo (distGHisto w) (distGFutu m)

-- | Mendler-style iteration, a restriction of general recursion in which the
-- recursive calls can only be applied to the recursive position. Equivalent to
-- a 'cata'.
--
-- Contrast the following with the example for 'cata': instead of already
-- having the sum for the tail of the list, we have an opaque version of the
-- rest of the list, and a function which can compute its sum.
--
-- > -- |
-- > -- >>> sum $ refix [1,2,3]
-- > -- 6
-- > sum :: Fix (ListF Int) -> Int
-- > sum = mcata $ \recur -> \case
-- >   Nil       -> 0
-- >   Cons x xs -> x + recur xs
mcata :: (forall y. (y -> c) -> f y -> c) -> Fix f -> c
mcata psi = psi (mcata psi) . unfix

-- | Mendler-style course-of-value iteration, a restriction of general
-- recursion in which the recursive calls can only be applied to smaller terms.
-- Equivalent to 'histo' in terms of expressiveness, but note that overlapping
-- sub-problems aren't automatically cached by the 'Cofree'.
--
-- Contrast the following with the example for 'histo': instead of already
-- having the solution for the tail of the tail of the list, we unroll the list
-- in order to obtain an opaque version of the tail of the tail of the list,
-- and then we recur on it.
--
-- > -- |
-- > -- >>> pairs $ refix [1,2,3,4]
-- > -- Just [(1,2),(3,4)]
-- > -- >>> pairs $ refix [1,2,3,4,5]
-- > -- Nothing
-- > pairs :: Fix (ListF Int) -> Maybe [(Int,Int)]
-- > pairs = mhisto $ \recur unroll -> \case
-- >   Nil       -> Just []
-- >   Cons x xs -> case unroll xs of
-- >     Nil       -> Nothing
-- >     Cons y ys -> ((x,y) :) <$> recur ys
mhisto :: (forall y. (y -> c) -> (y -> f y) -> f y -> c) -> Fix f -> c
mhisto psi = psi (mhisto psi) unfix . unfix

-- | Elgot algebras, a variant of 'hylo' in which the anamorphism side may
-- decide to stop unfolding and to produce a solution instead. Useful when the
-- base functor does not have a constructor for the base case.
--
-- For example, in the following implementation of @fib n@, we naively recur on
-- @n-1@ and @n-2@ until we hit the base case, at which point we stop
-- unfolding. With 'hylo', we would use 'Branch' to recur and 'Leaf' to stop
-- unfolding, whereas with 'elgot' we can use 'Pair', a variant of 'TreeF'
-- which does not have a 'Leaf'-like constructor for the base case.
--
-- > data Pair a = Pair a a
-- >   deriving Functor
-- >
-- > -- |
-- > -- >>> fmap fib [0..8]
-- > -- [1,1,2,3,5,8,13,21,34]
-- > fib :: Int -> Integer
-- > fib = elgot merge split where
-- >   split :: Int -> Either Integer (Pair Int)
-- >   split 0 = Left 1
-- >   split 1 = Left 1
-- >   split n = Right $ Pair (n-1) (n-2)
-- >
-- >   merge :: Pair Integer -> Integer
-- >   merge (Pair x y) = x + y
elgot :: Functor f => (f a -> a) -> (b -> Either a (f b)) -> b -> a
elgot phi psi = h where h = (id ||| phi . fmap h) . psi

-- | Elgot coalgebras, a variant of 'hylo' in which the catamorphism side also
-- has access to the seed which produced the sub-tree at that recursive
-- position. See <http://comonad.com/reader/2008/elgot-coalgebras/>
--
-- Contrast the following with the example for 'elgot': the base case is
-- detected while folding instead of while unfolding.
--
-- > -- |
-- > -- >>> fmap fib [0..8]
-- > -- [1,1,2,3,5,8,13,21,34]
-- > fib :: Int -> Integer
-- > fib = coelgot merge split where
-- >   split :: Int -> Pair Int
-- >   split n = Pair (n-1) (n-2)
-- >
-- >   merge :: (Int, Pair Integer) -> Integer
-- >   merge (0, _) = 1
-- >   merge (1, _) = 1
-- >   merge (_, Pair x y) = x + y
coelgot :: Functor f => ((a, f b) -> b) -> (a -> f a) -> a -> b
coelgot phi psi = h where h = phi . (id &&& fmap h . psi)

-- | The infamous "zygohistomorphic prepromorphism". There is nothing special
-- about this particular construction, it just happens to have a name which
-- sounds like gobbledygook, making it a prime target for jokes such as
-- <http://www.haskell.org/haskellwiki/Zygohistomorphic_prepromorphisms>.
--
-- Once you become familiar with the vocabulary of this library, the name no
-- longer sounds alien and is instead a very concise description of what it
-- does:
--
-- * It is a prepromorphism, meaning that it takes a recursive data structure
--   of type @t@, such as a list or a tree, and applies the
--   @forall c. Base t c -> Base t c@ transformation /n/ times at depth /n/.
--   The transformed results are then combined into a final solution of type
--   @a@ by applying the @Base t (EnvT b (Cofree (Base t)) a) -> a@ function
--   repeatedly, folding the recursive structure down to a single value. This
--   function is called an "algebra", and the other bullet points explain the
--   various part of its complicated type. See 'prepro'.
-- * It is zygomorphic, meaning that an auxiliary @Base t b -> b@ function
--   combines the transformed values into an auxiliary solution of type @b@.
--   The @EnvT b@ gives the algebra access to those auxiliary results. See
--   'zygo'.
-- * It is histomorphic, meaning that a @Cofree (Base t)@ gives the algebra
--   access to the solutions it previously computed for all the descendents of
--   the tree-like data structure being folded, not just those for the
--   immediate children. See 'histo'.
--
-- Here is an example function which uses all of those features:
--
-- * It uses indentation to illustrate nesting, that is, it applies an
--   indentation function /n/ times at depth /n/.
-- * It uses an auxiliary @TreeF String String -> String@ function to compute
--   the header of a group, which we choose to be the prefix shared by all
--   sub-trees.
-- * It alternates between two bullet styles, by looking at the solutions
--   computed two levels below.
--
-- > -- |
-- > -- >>> let tree = ((leaf "0.1.1.1" `branch` leaf "0.1.1.2") `branch` leaf "0.1.2") `branch` (leaf "0.2.1" `branch` leaf "0.2.2")
-- > -- >>> putStrLn (alternateBullets tree)
-- > -- * 0.
-- > --   - 0.1.
-- > --   * 0.1.1.
-- > --       - 0.1.1.1
-- > --       - 0.1.1.2
-- > --     * 0.1.2
-- > --   - 0.2.
-- > --     * 0.2.1
-- > --     * 0.2.2
-- > --
-- > alternateBullets :: Tree String -> String
-- > alternateBullets = zygoHistoPrepro mergeHeaders indent starThenDash
-- >
-- > starThenDash :: TreeF String (EnvT String (Cofree (TreeF String)) String) -> String
-- > starThenDash (Leaf s) = addBullet '*' s
-- > starThenDash (Branch (EnvT headerL cofreeL)
-- >                      (EnvT headerR cofreeR))
-- >   = addBullet '*' (mergeHeaders (Branch headerL headerR)) ++ "\n"
-- >  ++ dashThenStar headerL cofreeL ++ "\n"
-- >  ++ dashThenStar headerR cofreeR
-- >
-- > dashThenStar :: String -> Cofree (TreeF String) String -> String
-- > dashThenStar _ (_ :< Leaf s) = addBullet '-' s
-- > dashThenStar header (_ :< Branch (sL :< _) (sR :< _))
-- >   = addBullet '-' header ++ "\n"
-- >  ++ sL ++ "\n"
-- >  ++ sR
-- >
-- > -- |
-- > -- >>> addBullet '*' "   foo"
-- > -- "   * foo"
-- > addBullet :: Char -> String -> String
-- > addBullet bullet line = takeWhile (== ' ') line
-- >                      ++ (bullet:" ")
-- >                      ++ dropWhile (== ' ') line
--
-- Notice that the indentation of @"* 0.1.1."@ is off by one! This is because
-- the comonad-based implementation of 'zygoHistoPrepro' is
-- <https://github.com/ekmett/recursion-schemes/issues/50 subtly incorrect>.
zygoHistoPrepro
  :: (Corecursive t, Recursive t)
  => (Base t b -> b)
  -> (forall c. Base t c -> Base t c)
  -> (Base t (EnvT b (Cofree (Base t)) a) -> a)
  -> t
  -> a
zygoHistoPrepro f g t = gprepro (distZygoT f distHisto) g t

-------------------------------------------------------------------------------
-- Effectful combinators
-------------------------------------------------------------------------------

-- | Effectful 'fold'.
--
-- This is a type specialisation of 'cata'.
--
-- An example terminating a recursion immediately:
--
-- >>> cataA (\alg -> case alg of { Nil -> pure (); Cons a _ -> Const [a] })  "hello"
-- Const "h"
--
cataA :: (Recursive t) => (Base t (f a) -> f a) -> t -> f a
cataA = cata

-- | An effectful version of 'hoist'.
--
-- Properties:
--
-- @
-- 'transverse' 'sequenceA' = 'pure'
-- @
--
-- Examples:
--
-- The weird type of first argument allows user to decide
-- an order of sequencing:
--
-- >>> transverse (\x -> print (void x) *> sequence x) "foo" :: IO String
-- Cons 'f' ()
-- Cons 'o' ()
-- Cons 'o' ()
-- Nil
-- "foo"
--
-- >>> transverse (\x -> sequence x <* print (void x)) "foo" :: IO String
-- Nil
-- Cons 'o' ()
-- Cons 'o' ()
-- Cons 'f' ()
-- "foo"
--
transverse :: (Recursive s, Corecursive t, Functor f)
           => (forall a. Base s (f a) -> f (Base t a)) -> s -> f t
transverse n = cata (fmap embed . n)

-------------------------------------------------------------------------------
-- Not exposed anywhere
-------------------------------------------------------------------------------

-- | Read a list (using square brackets and commas), given a function
-- for reading elements.
_readListWith :: ReadS a -> ReadS [a]
_readListWith rp =
    readParen False (\r -> [pr | ("[",s) <- lex r, pr <- readl s])
  where
    readl s = [([],t) | ("]",t) <- lex s] ++
        [(x:xs,u) | (x,t) <- rp s, (xs,u) <- readl' t]
    readl' s = [([],t) | ("]",t) <- lex s] ++
        [(x:xs,v) | (",",t) <- lex s, (x,u) <- rp t, (xs,v) <- readl' u]
