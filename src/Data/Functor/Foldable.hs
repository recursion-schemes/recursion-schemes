{-# LANGUAGE TypeFamilies, Rank2Types, FlexibleContexts, FlexibleInstances, GADTs, StandaloneDeriving, UndecidableInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ScopedTypeVariables, DefaultSignatures, MultiParamTypeClasses, TypeOperators #-}

-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2008-2015 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  : "Samuel Gélineau" <gelisam@gmail.com>,
--               "Luc Tielen" <luc.tielen@gmail.com>,
--               "Ryan Scott" <ryan.gl.scott@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
----------------------------------------------------------------------------
module Data.Functor.Foldable
  (
  -- * Base functors
    Base
  , ListF(..)
  -- * Type classes
  , Recursive(project)
  , Corecursive(embed)
  -- * Folding functions
  -- $foldingFunctions
  , fold
  , cata
  , cataA
  , para
  , histo
  , zygo
  , accu
  -- * Unfolding functions
  , unfold
  , ana
  , apo
  , futu
  -- * Combining unfolds and folds
  , refold
  , hylo
  , chrono
  -- * Changing representation
  , refix
  , hoist
  , transverse
  , cotransverse
  -- * Advanced usage
  -- ** Mendler-style recursion-schemes
  , mcata
  , mpara
  , mhisto
  , mzygo
  , mana
  , mapo
  , mfutu
  -- ** Fokkinga's recursion-schemes
  , prepro
  , postpro
  -- ** Elgot (co)algebras
  , elgot
  , coelgot
  -- ** Generalized recursion-schemes
  , gfold
  , gcata
  , gpara
  , ghisto
  , gzygo
  , gunfold
  , gana
  , gapo
  , gfutu
  , grefold
  , ghylo
  , gchrono
  , gprepro
  , gpostpro
  , distCata
  , distPara
  , distParaT
  , distHisto
  , distGHisto
  , distZygo
  , distZygoT
  , distAna
  , distApo
  , distGApo
  , distGApoT
  , distFutu
  , distGFutu
  -- ** Zygohistomorphic prepromorphisms
  , zygoHistoPrepro
  ) where

import Control.Applicative
import Control.Comonad
import Control.Comonad.Trans.Class
import Control.Comonad.Trans.Env (EnvT(..))
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
import Data.Functor.Compose (Compose(..))
import Data.List.NonEmpty(NonEmpty((:|)), nonEmpty, toList)
import Data.Tree (Tree (..))
import GHC.Generics (Generic (..), M1 (..), V1, U1, K1 (..), (:+:) (..), (:*:) (..))
import Numeric.Natural
import Prelude

import           Data.Functor.Base hiding (head, tail)
import qualified Data.Functor.Base as NEF (NonEmptyF(..))

import Data.Fix (Fix (..), unFix, Mu (..), Nu (..))

-- $setup
-- >>> :set -XDeriveFunctor -XScopedTypeVariables -XLambdaCase -XGADTs -XFlexibleContexts
-- >>> import Control.Applicative (Const (..), Applicative (..))
-- >>> import Control.Comonad
-- >>> import Control.Comonad.Cofree (Cofree(..))
-- >>> import Control.Monad (void)
-- >>> import Control.Monad.Trans.Reader (Reader, ask, local, runReader)
-- >>> import Data.Char (toUpper)
-- >>> import Data.Fix (Fix (..))
-- >>> import Data.Foldable (traverse_)
-- >>> import Data.List (intercalate, partition)
-- >>> import Data.List.NonEmpty (NonEmpty (..))
-- >>> import Data.Maybe (maybeToList)
-- >>> import Data.Tree (Tree (..), drawTree)
-- >>> import Numeric.Natural
--
-- >>> import Data.Functor.Base
--
-- >>> let showTree = putStrLn . go where go (Node x xs) = if null xs then x else "(" ++ unwords (x : map go xs) ++ ")"
--
-- >>> let myTree = Node 0 [Node 1 [], Node 2 [], Node 3 [Node 31 [Node 311 [Node 3111 [], Node 3112 []]]]]

-- $foldingFunctions
-- Folding functions allow you to reduce a recursive structure down to a value. The value can be a simple type such as 'Int' or 'String', or it can also be a recursive structure. Each of the functions below will be accompanied by an example which folds the following @Tree Int@ down to some 'String'.
--
-- >>> putStr $ drawTree $ fmap show myTree
-- 0
-- |
-- +- 1
-- |
-- +- 2
-- |
-- `- 3
--    |
--    `- 31
--       |
--       `- 311
--          |
--          +- 3111
--          |
--          `- 3112

-- | Obtain the base functor for a recursive datatype.
--
-- The core idea of this library is that instead of writing recursive functions
-- on a recursive datatype, we prefer to write non-recursive functions on a
-- related, non-recursive datatype we call the "base functor".
--
-- For example, @[a]@ is a recursive type, and its corresponding base functor is
-- @'ListF' a@:
--
-- @
-- data 'ListF' a b = 'Nil' | 'Cons' a b
-- type instance 'Base' [a] = 'ListF' a
-- @
--
-- The relationship between those two types is that if we replace @b@ with
-- @'ListF' a@, we obtain a type which is isomorphic to @[a]@.
--
type family Base t :: * -> *

-- | A recursive datatype which can be unrolled one recursion layer at a time.
--
-- For example, a value of type @[a]@ can be unrolled into a @'ListF' a [a]@.
-- If that unrolled value is a 'Cons', it contains another @[a]@ which can be
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
  default project :: (Generic t, Generic (Base t t), GCoerce (Rep t) (Rep (Base t t))) => t -> Base t t
  project = to . gcoerce . from

  -- | An alias for 'fold'.
  --
  -- 'fold' is by far the most common recursion-scheme, because working one layer at a time is the most common strategy for writing a recursive function. But there are also other, rarer strategies. Researchers have given names to the most common strategies, and their name for 'fold' is "catamorphism". They also give its @Base t a -> a@ argument a special name, "(@Base t@)-algebra". More generally, a function of the form @f a -> a@ is called an "f-algebra".
  --
  -- The names might seem intimidating at first, but using the standard nomenclature has benefits. If you program with others, it can be useful to have a shared vocabulary to refer to those recursion patterns. For example, you can discuss which type of recursion is the most appropriate for the problem at hand. Names can also help to structure your thoughts while writing recursive functions.
  --
  -- The rest of this module lists a few of the other recursion-schemes which are common enough to have a name. In this section, we restrict our attention to those which fold a recursive structure down to a value. In the examples all functions will be of type @Tree Int -> String@.
  cata :: (Base t a -> a) -> t -> a
  cata f = c where c = f . fmap c . project

  -- | A variant of 'cata' in which recursive positions also include the
  -- original sub-tree, in addition to the result of folding that sub-tree.
  --
  -- For our running example, let's add a number to each node indicating how
  -- many children are below it. To do so, we will need to count those nodes
  -- from the original sub-tree.
  --
  -- >>> :{
  -- let pprint4 :: Tree Int -> String
  --     pprint4 = flip runReader 0 . para go
  --       where
  --         go :: TreeF Int (Tree Int, Reader Int String)
  --            -> Reader Int String
  --         go (NodeF i trss) = do
  --           -- trss :: [(Tree Int, Reader Int String)]
  --           -- ts   :: [Tree Int]
  --           -- rss  :: [Reader Int String]
  --           -- ss   :: [String]
  --           let (ts, rss) = unzip trss
  --           let count = sum $ fmap length ts
  --           ss <- local (+ 2) $ sequence rss
  --           indent <- ask
  --           let s = replicate indent ' '
  --                ++ "* " ++ show i
  --                ++ " (" ++ show count ++ ")"
  --           pure $ intercalate "\n" (s : ss)
  -- :}
  --
  -- >>> putStrLn $ pprint4 myTree
  -- * 0 (7)
  --   * 1 (0)
  --   * 2 (0)
  --   * 3 (4)
  --     * 31 (3)
  --       * 311 (2)
  --         * 3111 (0)
  --         * 3112 (0)
  --
  -- One common use for 'para' is to construct a new tree which reuses most of
  -- the sub-trees from the original. In the following example, we insert a new
  -- node under the leftmost leaf. This requires allocating new nodes along a
  -- path from the root to that leaf, while keeping every other sub-tree
  -- untouched.
  --
  -- >>> :{
  -- let insertLeftmost :: Int -> Tree Int -> Tree Int
  --     insertLeftmost new = para go
  --       where
  --         go :: TreeF Int (Tree Int, Tree Int)
  --            -> Tree Int
  --         go (NodeF i []) = Node i [Node new []]
  --         go (NodeF i ((_orig, recur) : tts))
  --             -- tts :: [(Tree Int, Tree Int)]
  --           = let (origs, _recurs) = unzip tts
  --             in Node i (recur : origs)
  -- :}
  --
  -- >>> putStrLn $ pprint4 $ insertLeftmost 999 myTree
  -- * 0 (8)
  --   * 1 (1)
  --     * 999 (0)
  --   * 2 (0)
  --   * 3 (4)
  --     * 31 (3)
  --       * 311 (2)
  --         * 3111 (0)
  --         * 3112 (0)
  para :: (Base t (t, a) -> a) -> t -> a
  para t = p where p x = t . fmap ((,) <*> p) $ project x

  gpara :: (Corecursive t, Comonad w) => (forall b. Base t (w b) -> w (Base t b)) -> (Base t (EnvT t w a) -> a) -> t -> a
  gpara t = gzygo embed t

  -- | Fokkinga's prepromorphism
  prepro
    :: Corecursive t
    => (forall b. Base t b -> Base t b)
    -> (Base t a -> a)
    -> t
    -> a
  prepro e f = c where c = f . fmap (c . hoist e) . project

  --- | A generalized prepromorphism
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

-- | A fold with an accumulation parameter
--
-- __An example is reversing a list__
--
-- First we define an accumulation strategy, i.e. how we accumulate
-- in each recursion step. In this case we will call it @consStrategy@.
-- Note that this defines how we accumulate the parameter in /any/
-- @ListF@-algebra (hence the carrier @b@).
--
-- >>> :{
-- let consStrategy :: [a] -> ListF a b ->  ListF a ([a], b)
--     consStrategy acc = \case
--       Nil -> Nil
--       Cons a as -> Cons a (a : acc, as)
-- :}
--
-- Next, we define the @reverse'@ fuction that `accu`-folds the
-- an algebra that also takes the accumulating parameter.
--
-- >>> :{
-- let reverse' :: [a] -> [a]
--     reverse' = accu consStrategy alg []
--       where
--         alg acc = \case
--           Nil -> acc
--           Cons _ as -> as
-- :}
--
-- >>> reverse' [1..4]
-- [4,3,2,1]
--
-- __An example of using the same strategy for different `accu`-folds__
--
-- Here, we will define an accumulation strategy that sums the
-- elements of the list and then use it in two `accu`-folds.
-- The first is to calculate the running sum of a list of `Num`
-- elements, while the second sums the running sum multiplied with
-- the current element.
--
-- First, we define the strategy as follows (note again that the
-- carrier is /any/ @b@):
--
-- >>> :{
-- let sumStrategy :: (Num a) => a -> ListF a b -> ListF a (a, b)
--     sumStrategy acc = \case
--       Nil -> Nil
--       Cons a as -> Cons a (a + acc, as)
-- :}
--
-- The running sum fold we define as follows:
--
-- >>> :{
-- let runningSum :: (Num a) => [a] -> [a]
--     runningSum = accu sumStrategy alg 0
--       where
--         alg acc = \case
--           Nil -> [acc]
--           Cons _ as -> acc : as
-- :}
--
-- >>> runningSum [1..10]
-- [0,1,3,6,10,15,21,28,36,45,55]
--
-- Now, we can reuse @sumStrategy@ to define another `accu`-fold:
--
-- >>> :{
-- let runningSumMultiply :: forall a. (Num a, Ord a) => [a] -> a
--     runningSumMultiply = accu sumStrategy alg 0
--       where
--         alg acc = \case
--           Nil -> 0
--           Cons s as -> s * acc + as
-- :}
--
-- >>> runningSumMultiply [1..5]
-- 85
accu
  :: forall t p a. (Functor (Base t), Recursive t)
  => (forall x. p -> Base t x -> Base t (p, x))
  -> (p -> Base t a -> a)
  -> p
  -> t
  -> a
accu st alg p t = c where c = alg p (fmap (uncurry (accu st alg)) (st p (project t)))

-- | A recursive datatype which can be rolled up one recursion layer at a time.
--
-- For example, a value of type @'ListF' a [a]@ can be rolled up into a @[a]@.
-- This @[a]@ can then be used in a 'Cons' to construct another @'ListF' a [a]@,
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
  default embed :: (Generic t, Generic (Base t t), GCoerce (Rep (Base t t)) (Rep t)) => Base t t -> t
  embed = to . gcoerce . from

  -- | An alias for 'unfold'.
  ana
    :: (a -> Base t a) -- ^ a (Base t)-coalgebra
    -> a               -- ^ seed
    -> t               -- ^ resulting fixed point
  ana g = a where a = embed . fmap a . g

  apo :: (a -> Base t (Either t a)) -> a -> t
  apo g = a where a = embed . (fmap (either id a)) . g

  -- | Fokkinga's postpromorphism
  postpro
    :: Recursive t
    => (forall b. Base t b -> Base t b) -- natural transformation
    -> (a -> Base t a)                  -- a (Base t)-coalgebra
    -> a                                -- seed
    -> t
  postpro e g = a where a = embed . fmap (hoist e . a) . g

  -- | A generalized postpromorphism
  gpostpro
    :: (Recursive t, Monad m)
    => (forall b. m (Base t b) -> Base t (m b)) -- distributive law
    -> (forall c. Base t c -> Base t c)         -- natural transformation
    -> (a -> Base t (m a))                      -- a (Base t)-m-coalgebra
    -> a                                        -- seed
    -> t
  gpostpro k e g = a . return where a = embed . fmap (hoist e . a . join) . k . liftM g

-- | An alias for 'refold'.
hylo :: Functor f => (f b -> b) -> (a -> f a) -> a -> b
hylo f g = h where h = f . fmap h . g

-- | Folds a recursive type down to a value, one layer at a time.
--
-- >>> :{
-- let mySum :: [Int] -> Int
--     mySum = fold $ \case
--       Nil -> 0
--       Cons x sumXs -> x + sumXs
-- :}
--
-- >>> mySum [10,11,12]
-- 33
--
-- In our running example, one layer consists of an 'Int' and a list of recursive positions. In @Tree Int@, those recursive positions contain sub-trees of type @Tree Int@. Since we are working one layer at a time, the @Base t a -> a@ function is not given a @Tree Int@, but a @TreeF Int String@. That is, each recursive position contains the 'String' resulting from recursively folding the corresponding sub-tree.
--
-- >>> :{
-- let pprint1 :: Tree Int -> String
--     pprint1 = fold $ \case
--       NodeF i [] -> show i
--       NodeF i ss -> show i ++ ": [" ++ intercalate ", " ss ++ "]"
-- :}
--
-- >>> putStrLn $ pprint1 myTree
-- 0: [1, 2, 3: [31: [311: [3111, 3112]]]]
--
-- More generally, the 't' argument is the recursive value, the 'a' is the final result, and the @Base t a -> a@ function explains how to reduce a single layer full of recursive results down to a result.
fold :: Recursive t => (Base t a -> a) -> t -> a
fold = cata

-- | A generalization of 'unfoldr'. The starting seed is expanded into a base
-- functor whose recursive positions contain more seeds, which are themselves
-- expanded, and so on.
--
-- >>> :{
-- >>> let ourEnumFromTo :: Int -> Int -> [Int]
-- >>>     ourEnumFromTo lo hi = unfold go lo where
-- >>>         go i = if i > hi then Nil else Cons i (i + 1)
-- >>> :}
--
-- >>> ourEnumFromTo 1 4
-- [1,2,3,4]
unfold :: Corecursive t => (a -> Base t a) -> a -> t
unfold = ana

-- | An optimized version of @fold f . unfold g@.
--
-- Useful when your recursion structure is shaped like a particular recursive
-- datatype, but you're neither consuming nor producing that recursive datatype.
-- For example, the recursion structure of quick sort is a binary tree, but its
-- input and output is a list, not a binary tree.
--
-- >>> data BinTreeF a b = Tip | Branch b a b deriving (Functor)
--
-- >>> :{
-- >>> let quicksort :: Ord a => [a] -> [a]
-- >>>     quicksort = refold merge split where
-- >>>         split []     = Tip
-- >>>         split (x:xs) = let (l, r) = partition (<x) xs in Branch l x r
-- >>>
-- >>>         merge Tip            = []
-- >>>         merge (Branch l x r) = l ++ [x] ++ r
-- >>> :}
--
-- >>> quicksort [1,5,2,8,4,9,8]
-- [1,2,4,5,8,8,9]
refold :: Functor f => (f b -> b) -> (a -> f a) -> a -> b
refold = hylo

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

type instance Base (Tree a) = TreeF a
instance Recursive (Tree a) where
  project (Node x xs) = NodeF x xs
instance Corecursive (Tree a) where
  embed (NodeF x xs) = Node x xs

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

-- | A generalized catamorphism
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

-- | A generalized anamorphism
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

-- | A generalized hylomorphism
grefold, ghylo
  :: (Comonad w, Functor f, Monad m)
  => (forall c. f (w c) -> w (f c))
  -> (forall d. m (f d) -> f (m d))
  -> (f (w b) -> b)
  -> (a -> f (m a))
  -> a
  -> b
ghylo w m f g = f . fmap (hylo alg coalg) . g where
  coalg = fmap join . m . liftM g
  alg   = fmap f . w . fmap duplicate
grefold w m f g a = ghylo w m f g a

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

type instance Base (Fix f) = f
instance Functor f => Recursive (Fix f) where
  project (Fix a) = a
instance Functor f => Corecursive (Fix f) where
  embed = Fix

-- | Convert from one recursive type to another.
--
-- >>> showTree $ hoist (\(NonEmptyF h t) -> NodeF [h] (maybeToList t)) ( 'a' :| "bcd")
-- (a (b (c d)))
--
hoist :: (Recursive s, Corecursive t)
      => (forall a. Base s a -> Base t a) -> s -> t
hoist n = cata (embed . n)

-- | Convert from one recursive representation to another.
--
-- >>> refix ["foo", "bar"] :: Fix (ListF String)
-- Fix (Cons "foo" (Fix (Cons "bar" (Fix Nil))))
--
refix :: (Recursive s, Corecursive t, Base s ~ Base t) => s -> t
refix = cata embed

-------------------------------------------------------------------------------
-- Lambek
-------------------------------------------------------------------------------

-- | Lambek's lemma provides a default definition for 'project' in terms of 'cata' and 'embed'
lambek :: (Recursive t, Corecursive t) => (t -> Base t t)
lambek = cata (fmap embed)

-- | The dual of Lambek's lemma, provides a default definition for 'embed' in terms of 'ana' and 'project'
colambek :: (Recursive t, Corecursive t) => (Base t t -> t)
colambek = ana (fmap project)

type instance Base (Mu f) = f
instance Functor f => Recursive (Mu f) where
  project = lambek
  cata f (Mu g) = g f
instance Functor f => Corecursive (Mu f) where
  embed m = Mu (\f -> f (fmap (fold f) m))

type instance Base (Nu f) = f
instance Functor f => Corecursive (Nu f) where
  embed = colambek
  ana = Nu
instance Functor f => Recursive (Nu f) where
  project (Nu f a) = Nu f <$> f a

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

-- TODO: link from 'para' to 'zygo'
zygo :: Recursive t => (Base t b -> b) -> (Base t (b, a) -> a) -> t -> a
zygo f = gfold (distZygo f)

distZygo
  :: Functor f
  => (f b -> b)             -- An f-algebra
  -> (f (b, a) -> (b, f a)) -- ^ A distributive for semi-mutual recursion
distZygo g m = (g (fmap fst m), fmap snd m)

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

-- | A variant of 'cata' which includes the results of all the
-- descendents, not just the direct children.
--
-- Like 'para', a sub-tree is provided for each recursive position. Each
-- node in that sub-tree is annotated with the result for that
-- descendent. The 'Cofree' type is used to add those annotations.
--
-- For our running example, let's recreate GitHub's directory compression
-- algorithm. Notice that in [the repository for this
-- package](https://github.com/recursion-schemes/recursion-schemes), GitHub
-- displays @src\/Data\/Functor@, not @src@:
--
-- ![GitHub's code page](docs/github-compression.png)
--
-- GitHub does this because @src@ only contains one entry: @Data@. Similarly,
-- @Data@ only contains one entry: @Functor@. @Functor@ contains several
-- entries, so the compression stops there. This helps users get to the
-- interesting folders more quickly.
--
-- Before we use 'histo', we need to define a helper function 'rollup'.
-- It collects nodes until it reaches a node which doesn't have exactly one
-- child. It also returns the labels of that node's children.
--
-- >>> :{
-- let rollup :: [Cofree (TreeF node) label]
--            -> ([node], [label])
--     rollup [_ :< NodeF node cofrees] =
--       let (nodes, label) = rollup cofrees
--       in (node : nodes, label)
--     rollup cofrees =
--       ([], fmap extract cofrees)
-- :}
--
-- >>> let foobar xs = 1 :< NodeF "foo" [2 :< NodeF "bar" xs]
-- >>> rollup [foobar []]
-- (["foo","bar"],[])
-- >>> rollup [foobar [3 :< NodeF "baz" [], 4 :< NodeF "quux" []]]
-- (["foo","bar"],[3,4])
--
-- The value @foobar []@ can be interpreted as the tree @NodeF "foo"
-- [NodeF "bar" []]@, plus two annotations. The @"foo"@ node is annotated
-- with @1@, while the @"bar"@ node is annotated with @2@. When we call
-- 'histo' below, those annotations are recursive results of type @Int ->
-- String@.
--
-- >>> :{
-- let pprint5 :: Tree Int -> String
--     pprint5 t = histo go t 0
--       where
--         go :: TreeF Int (Cofree (TreeF Int) (Int -> String))
--            -> Int -> String
--         go (NodeF node cofrees) indent
--             -- cofrees :: [Cofree (TreeF Int) (Int -> String)]
--             -- fs :: [Int -> String]
--           = let indent' = indent + 2
--                 (nodes, fs) = rollup cofrees
--                 ss = map (\f -> f indent') fs
--                 s = replicate indent ' '
--                  ++ "* " ++ intercalate " / " (fmap show (node : nodes))
--             in intercalate "\n" (s : ss)
-- :}
--
-- >>> putStrLn $ pprint5 myTree
-- * 0
--   * 1
--   * 2
--   * 3 / 31 / 311
--     * 3111
--     * 3112
--
-- One common use for 'histo' is to cache the value computed for smaller
-- sub-trees. In the Fibonacci example below, the recursive type is 'Natural',
-- which is isomorphic to @[()]@. Our annotated sub-tree is thus isomorphic to
-- a list of annotations. In our case, each annotation is the result which was
-- computed for a smaller number. We thus have access to a list which caches
-- all the Fibonacci numbers we have computed so far.
--
-- >>> :{
-- let fib :: Natural -> Integer
--     fib = histo go
--       where
--         go :: Maybe (Cofree Maybe Integer) -> Integer
--         go Nothing = 1
--         go (Just (_ :< Nothing)) = 1
--         go (Just (fibNMinus1 :< Just (fibNMinus2 :< _)))
--           = fibNMinus1 + fibNMinus2
-- :}
--
-- >>> fmap fib [0..10]
-- [1,1,2,3,5,8,13,21,34,55,89]
--
-- In general, @Cofree f a@ can be thought of as a cache that has the same
-- shape as the recursive structure which was given as input.
histo :: Recursive t => (Base t (Cofree (Base t) a) -> a) -> t -> a
histo = gcata distHisto

ghisto :: (Recursive t, Comonad w) => (forall b. Base t (w b) -> w (Base t b)) -> (Base t (CofreeT (Base t) w a) -> a) -> t -> a
ghisto g = gcata (distGHisto g)

distHisto :: Functor f => f (Cofree f a) -> Cofree f (f a)
distHisto fc = fmap extract fc :< fmap (distHisto . Cofree.unwrap) fc

distGHisto :: (Functor f, Functor h) => (forall b. f (h b) -> h (f b)) -> f (CofreeT f h a) -> CofreeT f h (f a)
distGHisto k = d where d = CofreeT . fmap (\fc -> fmap CCTC.headF fc CCTC.:< fmap (d . CCTC.tailF) fc) . k . fmap runCofreeT

chrono :: Functor f => (f (Cofree f b) -> b) -> (a -> f (Free f a)) -> (a -> b)
chrono = ghylo distHisto distFutu

gchrono :: (Functor f, Functor w, Functor m, Comonad w, Monad m) =>
           (forall c. f (w c) -> w (f c)) ->
           (forall c. m (f c) -> f (m c)) ->
           (f (CofreeT f w b) -> b) -> (a -> f (FreeT f m a)) ->
           (a -> b)
gchrono w m = ghylo (distGHisto w) (distGFutu m)

-- | Mendler-style iteration
mcata :: (forall y. (y -> c) -> f y -> c) -> Fix f -> c
mcata psi = c where c = psi c . unFix

-- | Mendler-style recursion
--
-- @since 5.2.2
mpara :: (forall y. (y -> c) -> (y -> Fix f) -> f y -> c) -> Fix f -> c
mpara psi = c where c = psi c id . unFix

-- | Mendler-style semi-mutual recursion
--
-- @since 5.2.2
mzygo :: (forall y. (y -> b) -> f y -> b) -> (forall y. (y -> c) -> (y -> b) -> f y -> c) -> Fix f -> c
mzygo phi psi = c where c = psi c (mcata phi) . unFix

-- | Mendler-style course-of-value iteration
mhisto :: (forall y. (y -> c) -> (y -> f y) -> f y -> c) -> Fix f -> c
mhisto psi = c where c = psi c unFix . unFix

-- | Mendler-style coiteration
--
-- @since 5.2.2
mana :: (forall y. (x -> y) -> x -> f y) -> x -> Fix f
mana phi = c where c = Fix . phi c

-- | Mendler-style corecursion
--
-- @since 5.2.2
mapo :: (forall y. (Fix f -> y) -> (x -> y) -> x -> f y) -> x -> Fix f
mapo phi = c where c = Fix . phi id c

-- | Mendler-style course-of-values coiteration
--
-- @since 5.2.2
mfutu :: (forall y. (f y -> y) -> (x -> y) -> x -> f y) -> x -> Fix f
mfutu phi = c where c = Fix . phi Fix c

-- | Elgot algebras
elgot :: Functor f => (f a -> a) -> (b -> Either a (f b)) -> b -> a
elgot phi psi = h where h = (id ||| phi . fmap h) . psi

-- | Elgot coalgebras: <http://comonad.com/reader/2008/elgot-coalgebras/>
coelgot :: Functor f => ((a, f b) -> b) -> (a -> f a) -> a -> b
coelgot phi psi = h where h = phi . (id &&& fmap h . psi)

-- | Zygohistomorphic prepromorphisms:
--
-- A corrected and modernized version of <http://www.haskell.org/haskellwiki/Zygohistomorphic_prepromorphisms>
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

-- | A specialization of 'cata' for effectful folds.
--
-- 'cataA' is the same as 'cata', but with a more specialized type. The only
-- reason it exists is to make it easier to discover how to use this library
-- with effects.
--
-- For our running example, let's improve the output format of our
-- pretty-printer by using indentation. To do so, we will need to keep track of
-- the current indentation level. We will do so using a @Reader Int@ effect.
-- Our recursive positions will thus contain @Reader Int String@ actions, not
-- @String@s. This means we need to run those actions in order to get the
-- results.
--
-- >>> :{
-- let pprint2 :: Tree Int -> String
--     pprint2 = flip runReader 0 . cataA go
--       where
--         go :: TreeF Int (Reader Int String)
--            -> Reader Int String
--         go (NodeF i rss) = do
--           -- rss :: [Reader Int String]
--           -- ss  :: [String]
--           ss <- local (+ 2) $ sequence rss
--           indent <- ask
--           let s = replicate indent ' ' ++ "* " ++ show i
--           pure $ intercalate "\n" (s : ss)
-- :}
--
-- >>> putStrLn $ pprint2 myTree
-- * 0
--   * 1
--   * 2
--   * 3
--     * 31
--       * 311
--         * 3111
--         * 3112
--
-- The fact that the recursive positions contain 'Reader' actions instead of
-- 'String's gives us some flexibility. Here, we are able to increase the
-- indentation by running those actions inside a 'local' block. More generally,
-- we can control the order of their side-effects, interleave them with other
-- effects, etc.
--
-- A similar technique is to specialize 'cata' so that the result is a
-- function. This makes it possible for data to flow down in addition to up.
-- In this modified version of our running example, the indentation level flows
-- down from the root to the leaves, while the resulting strings flow up from
-- the leaves to the root.
--
-- >>> :{
-- let pprint3 :: Tree Int -> String
--     pprint3 t = cataA go t 0
--       where
--         go :: TreeF Int (Int -> String)
--            -> Int -> String
--         go (NodeF i fs) indent
--             -- fs :: [Int -> String]
--           = let indent' = indent + 2
--                 ss = map (\f -> f indent') fs
--                 s = replicate indent ' ' ++ "* " ++ show i
--             in intercalate "\n" (s : ss)
-- :}
--
-- >>> putStrLn $ pprint3 myTree
-- * 0
--   * 1
--   * 2
--   * 3
--     * 31
--       * 311
--         * 3111
--         * 3112
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

-- | A coeffectful version of 'hoist'.
--
-- Properties:
--
-- @
-- 'cotransverse' 'distAna' = 'runIdentity'
-- @
--
-- Examples:
--
-- Stateful transformations:
--
-- >>> :{
-- cotransverse
--   (\(u, b) -> case b of
--     Nil -> Nil
--     Cons x a -> Cons (if u then toUpper x else x) (not u, a))
--   (True, "foobar") :: String
-- :}
-- "FoObAr"
--
-- We can implement a variant of `zipWith`
--
-- >>> data Pair a = Pair a a deriving Functor
--
-- >>> :{
-- let zipWith' :: forall a b. (a -> a -> b) -> [a] -> [a] -> [b]
--     zipWith' f xs ys = cotransverse g (Pair xs ys) where
--       g :: Pair (ListF a c) -> ListF b (Pair c)
--       g (Pair Nil        _)          = Nil
--       g (Pair _          Nil)        = Nil
--       g (Pair (Cons x a) (Cons y b)) = Cons (f x y) (Pair a b)
--     :}
--
-- >>> zipWith' (*) [1,2,3] [4,5,6]
-- [4,10,18]
--
-- >>> zipWith' (*) [1,2,3] [4,5,6,8]
-- [4,10,18]
--
-- >>> zipWith' (*) [1,2,3,3] [4,5,6]
-- [4,10,18]
--
cotransverse :: (Recursive s, Corecursive t, Functor f)
             => (forall a. f (Base s a) -> Base t (f a)) -> f s -> t
cotransverse n = ana (n . fmap project)

-------------------------------------------------------------------------------
-- GCoerce
-------------------------------------------------------------------------------

class GCoerce f g where
    gcoerce :: f a -> g a

instance GCoerce f g => GCoerce (M1 i c f) (M1 i c' g) where
    gcoerce (M1 x) = M1 (gcoerce x)

-- R changes to/from P with GHC-7.4.2 at least.
instance GCoerce (K1 i c) (K1 j c) where
    gcoerce = K1 . unK1

instance GCoerce U1 U1 where
    gcoerce = id

instance GCoerce V1 V1 where
    gcoerce = id

instance (GCoerce f g, GCoerce f' g') => GCoerce (f :*: f') (g :*: g') where
    gcoerce (x :*: y) = gcoerce x :*: gcoerce y

instance (GCoerce f g, GCoerce f' g') => GCoerce (f :+: f') (g :+: g') where
    gcoerce (L1 x) = L1 (gcoerce x)
    gcoerce (R1 x) = R1 (gcoerce x)
