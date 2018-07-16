{-# LANGUAGE CPP, TypeFamilies, Rank2Types, FlexibleContexts, FlexibleInstances, GADTs, ScopedTypeVariables, StandaloneDeriving, UndecidableInstances #-}

-- explicit dictionary higher-kind instances are defined in
-- - base-4.9
-- - transformers >= 0.5
-- - transformes-compat >= 0.5 when transformers aren't 0.4
--
-- We don't always depend on transformers-compat, so we need a shim for its version check.
#ifndef MIN_VERSION_transformers_compat
#define MIN_VERSION_transformers_compat(x,y,z) 0
#endif

#define EXPLICIT_DICT_FUNCTOR_CLASSES (MIN_VERSION_base(4,9,0) || MIN_VERSION_transformers(0,5,0) || (MIN_VERSION_transformers_compat(0,5,0) && !MIN_VERSION_transformers(0,4,0)))

#define HAS_GENERIC (__GLASGOW_HASKELL__ >= 702)
#define HAS_GENERIC1 (__GLASGOW_HASKELL__ >= 706)

-- Polymorphic typeable
#define HAS_POLY_TYPEABLE MIN_VERSION_base(4,7,0)

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
  , Fix(..), unfix, hoistFix
  , Mu(..), hoistMu
  , Nu(..), hoistNu
  -- * Folding
  , Recursive(..)
  -- ** Combinators
  , gapo
  , gcata
  , zygo
  , gzygo
  , histo
  , ghisto
  , futu
  , gfutu
  , chrono
  , gchrono
  -- ** Gathering functions
  , Gather
  , gatherCata
  , gatherPara
  , gatherParaT
  , gatherZygo
  , gatherZygoT
  , gatherHisto
  , gatherGHisto
  -- * Unfolding
  , Corecursive(..)
  -- ** Combinators
  , gana
  -- ** Scattering functions
  , Scatter
  , scatterAna
  , scatterApo
  , scatterGApo
  , scatterGApoT
  , scatterFutu
  , scatterGFutu
  -- * Refolding
  , hylo
  , ghylo
  -- ** Changing representation
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
  ) where

import Control.Applicative
import Control.Comonad
import Control.Comonad.Cofree (Cofree(..))
import           Control.Comonad.Trans.Cofree (CofreeF, CofreeT(..))
import qualified Control.Comonad.Trans.Cofree as CCTC
import Control.Monad.Free (Free(..))
import qualified Control.Monad.Free.Church as CMFC
import           Control.Monad.Trans.Free (FreeF, FreeT(..))
import qualified Control.Monad.Trans.Free as CMTF
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

type family Base t :: * -> *

class Functor (Base t) => Recursive t where
  project :: t -> Base t t

  cata :: (Base t a -> a) -- ^ a (Base t)-algebra
       -> t               -- ^ fixed point
       -> a               -- ^ result
  cata f = c where c = f . fmap c . project

  para :: (Base t (t, a) -> a) -> t -> a
  para f = p where p x = f . fmap ((,) <*> p) $ project x

  gpara :: Corecursive t => Gather (Base t) a s -> (Base t (t, s) -> a) -> t -> a
  gpara = gzygo embed

  -- | Fokkinga's prepromorphism
  prepro
    :: Corecursive t
    => (forall b. Base t b -> Base t b)
    -> (Base t a -> a)
    -> t
    -> a
  prepro e f = c where c = f . fmap (c . cata (embed . e)) . project

  --- | A generalized prepromorphism
  gprepro
    :: forall a s. Corecursive t
    => Gather (Base t) a s
    -> (forall c. Base t c -> Base t c)
    -> (Base t s -> a)
    -> t
    -> a
  gprepro gather e0 f = f . fmap (go e0) . project where
    deeper :: (forall b. Base t b -> Base t b) -> (forall b. Base t b -> Base t b)
    deeper e = e . e0

    go :: (forall b. Base t b -> Base t b) -> t -> s
    go e = uncurry gather . (f &&& id) . fmap (go (deeper e)) . e . project

gatherPara :: Corecursive t => Gather (Base t) a (t, a)
gatherPara = gatherZygo embed

gatherParaT :: Corecursive t => Gather (Base t) a s -> Gather (Base t) a (t, s)
gatherParaT = gatherZygoT embed

class Functor (Base t) => Corecursive t where
  embed :: Base t t -> t
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
  postpro e g = a where a = embed . fmap (ana (e . project) . a) . g

  -- | A generalized postpromorphism
  gpostpro
    :: forall a s. Recursive t
    => Scatter (Base t) a s
    -> (forall c. Base t c -> Base t c)
    -> (a -> Base t s)
    -> a
    -> t
  gpostpro scatter e0 g = embed . fmap (go e0) . g where
    deeper :: (forall c. Base t c -> Base t c) -> (forall c. Base t c -> Base t c)
    deeper e = e . e0

    go :: (forall c. Base t c -> Base t c) -> s -> t
    go e = embed . e . fmap (go (deeper e)) . (g ||| id) . scatter

hylo :: Functor f => (f b -> b) -> (a -> f a) -> a -> b
hylo f g = h where h = f . fmap h . g

fold :: Recursive t => (Base t a -> a) -> t -> a
fold = cata

unfold :: Corecursive t => (a -> Base t a) -> a -> t
unfold = ana

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

#if EXPLICIT_DICT_FUNCTOR_CLASSES
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
  ana                  coalg = improveF . ana                  coalg
  postpro          nat coalg = improveF . postpro          nat coalg
  gpostpro scatter nat coalg = improveF . gpostpro scatter nat coalg

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
  :: forall t a s. Recursive t
  => Gather (Base t) a s
  -> (Base t s -> a)
  -> t
  -> a
gcata gather f = f . fmap go . project where
  go :: t -> s
  go = uncurry gather . (f &&& id) . fmap go . project
gfold gather f t = gcata gather f t

type Gather f a s = a -> f s -> s

gatherCata :: Gather f a a
gatherCata = const

-- | A generalized anamorphism
gunfold, gana
  :: forall t a s. Corecursive t
  => Scatter (Base t) a s
  -> (a -> Base t s)
  -> a
  -> t
gana scatter g = embed . fmap go . g where
  go :: s -> t
  go = embed . fmap go . (g ||| id) . scatter
gunfold scatter g t = gana scatter g t

type Scatter f a s = s -> Either a (f s)

scatterAna :: Functor f => Scatter f a a
scatterAna = Left

-- | A generalized hylomorphism
grefold, ghylo
  :: forall f a b s r. Functor f
  => Gather f b r
  -> Scatter f a s
  -> (f r -> b)
  -> (a -> f s)
  -> a
  -> b
ghylo gather scatter f g = f . fmap go . g where
  go :: s -> r
  go = uncurry gather . (f &&& id) . fmap go . (g ||| id) . scatter
grefold gather scatter f g a = ghylo gather scatter f g a

futu :: Corecursive t => (a -> Base t (Free (Base t) a)) -> a -> t
futu = gana scatterFutu

gfutu :: Corecursive t => Scatter (Base t) a s -> (a -> Base t (Free (Base t) s)) -> a -> t
gfutu scatter = gana (scatterGFutu scatter)

scatterFutu :: Functor f => Scatter f a (Free f a)
scatterFutu (Pure a)  = Left a
scatterFutu (Free ff) = Right ff

scatterGFutu :: Functor f => Scatter f a s -> Scatter f a (Free f s)
scatterGFutu scatter (Pure s)  = fmap Pure <$> scatter s
scatterGFutu _       (Free ff) = Right ff

-------------------------------------------------------------------------------
-- Fix
-------------------------------------------------------------------------------

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

refix :: (Recursive s, Corecursive t, Base s ~ Base t) => s -> t
refix = cata embed

toFix :: Recursive t => t -> Fix (Base t)
toFix = refix

fromFix :: Corecursive t => Fix (Base t) -> t
fromFix = refix

hoistFix :: Functor f
         => (forall a. f a -> g a) -> Fix f -> Fix g
hoistFix n = cata (Fix . n)


-------------------------------------------------------------------------------
-- Lambek
-------------------------------------------------------------------------------

-- | Lambek's lemma provides a default definition for 'project' in terms of 'cata' and 'embed'
lambek :: (Recursive t, Corecursive t) => (t -> Base t t)
lambek = cata (fmap embed)

-- | The dual of Lambek's lemma, provides a default definition for 'embed' in terms of 'ana' and 'project'
colambek :: (Recursive t, Corecursive t) => (Base t t -> t)
colambek = ana (fmap project)

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

hoistMu :: Functor f
        => (forall a. f a -> g a) -> Mu f -> Mu g
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

hoistNu :: Functor g
        => (forall a. f a -> g a) -> Nu f -> Nu g
hoistNu n (Nu next seed) = Nu (n . next) seed


zygo :: Recursive t => (Base t b -> b) -> (Base t (b, a) -> a) -> t -> a
zygo f = gfold (gatherZygo f)

gatherZygo
  :: Functor f
  => (f b -> b)        -- An f-algebra
  -> Gather f a (b, a) -- ^ A gathering function for semi-mutual recursion
gatherZygo g x fyx = (g $ fst <$> fyx, x)

gzygo
  :: Recursive t
  => (Base t b -> b)
  -> Gather (Base t) a s
  -> (Base t (b, s) -> a)
  -> t
  -> a
gzygo f gather = gfold (gatherZygoT f gather)

gatherZygoT
  :: Functor f
  => (f b -> b)
  -> Gather f a s      -- A base gathering function
  -> Gather f a (b, s) -- A new gathering function that adds semi-mutual recursion
gatherZygoT f gather x = (f . fmap fst) &&& (gather x . fmap snd)

gapo :: Corecursive t => (b -> Base t b) -> (a -> Base t (Either b a)) -> a -> t
gapo g = gunfold (scatterGApo g)

scatterApo :: Recursive t => Scatter (Base t) a (Either t a)
scatterApo = scatterGApo project

scatterGApo :: Functor f => (b -> f b) -> Scatter f a (Either b a)
scatterGApo g = scatterGApoT g scatterAna

scatterGApoT
  :: Functor f
  => (b -> f b)
  -> Scatter f a s
  -> Scatter f a (Either b s)
scatterGApoT g _       (Left  b) = Right $ Left <$> g b
scatterGApoT _ scatter (Right s) = fmap Right <$> scatter s

-- | Course-of-value iteration
histo :: Recursive t => (Base t (Cofree (Base t) a) -> a) -> t -> a
histo = gcata gatherHisto

ghisto :: Recursive t => Gather (Base t) a s -> (Base t (Cofree (Base t) s) -> a) -> t -> a
ghisto gather = gcata (gatherGHisto gather)

gatherHisto :: Functor f => Gather f a (Cofree f a)
gatherHisto = (:<)

gatherGHisto :: Functor f => Gather f a s -> Gather f a (Cofree f s)
gatherGHisto gather x fc = gather x (extract <$> fc) :< fc

chrono :: Functor f => (f (Cofree f b) -> b) -> (a -> f (Free f a)) -> (a -> b)
chrono = ghylo gatherHisto scatterFutu

gchrono :: Functor f =>
           Gather f b r ->
           Scatter f a s ->
           (f (Cofree f r) -> b) -> (a -> f (Free f s)) ->
           (a -> b)
gchrono gather scatter = ghylo (gatherGHisto gather) (scatterGFutu scatter)

-- | Mendler-style iteration
mcata :: (forall y. (y -> c) -> f y -> c) -> Fix f -> c
mcata psi = psi (mcata psi) . unfix

-- | Mendler-style course-of-value iteration
mhisto :: (forall y. (y -> c) -> (y -> f y) -> f y -> c) -> Fix f -> c
mhisto psi = psi (mhisto psi) unfix . unfix

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
  -> (Base t (b, Cofree (Base t) a) -> a)
  -> t
  -> a
zygoHistoPrepro f g t = gprepro (gatherZygoT f gatherHisto) g t

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
