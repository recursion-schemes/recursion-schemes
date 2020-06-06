{-# LANGUAGE CPP, TypeFamilies, Rank2Types, FlexibleContexts, FlexibleInstances, GADTs, StandaloneDeriving, UndecidableInstances #-}
#include "recursion-schemes-common.h"

#ifdef __GLASGOW_HASKELL__
{-# LANGUAGE DeriveDataTypeable #-}
#if __GLASGOW_HASKELL__ >= 800
{-# LANGUAGE ConstrainedClassMethods #-}
#endif
#if HAS_GENERIC
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ScopedTypeVariables, DefaultSignatures, MultiParamTypeClasses, TypeOperators #-}
#endif
#endif

-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2008-2015 Edward Kmett
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  : "Samuel Gélineau" <gelisam@gmail.com>,
--               "Oleg Grenrus" <oleg.grenrus@iki.fi>,
--               "Ryan Scott" <ryan.gl.scott@gmail.com>
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
  -- ** Distributive laws
  , distCata
  , distPara
  , distParaT
  , distZygo
  , distZygoT
  , distHisto
  , distGHisto
  , distFutu
  , distGFutu
  -- * Unfolding
  , Corecursive(..)
  -- ** Combinators
  , gana
  -- ** Distributive laws
  , distAna
  , distApo
  , distGApo
  , distGApoT
  -- * Refolding
  , hylo
  , ghylo
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
  , cotransverse
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
import Data.Tree (Tree (..))
import Text.Read
import Text.Show
#ifdef __GLASGOW_HASKELL__
import Data.Data hiding (gunfold)
#if HAS_POLY_TYPEABLE
#else
import qualified Data.Data as Data
#endif
#if HAS_GENERIC
import GHC.Generics (Generic (..), M1 (..), V1, U1, K1 (..), (:+:) (..), (:*:) (..))
#endif
#endif
import Numeric.Natural
import Prelude

import           Data.Functor.Base hiding (head, tail)
import qualified Data.Functor.Base as NEF (NonEmptyF(..))

-- $setup
-- >>> :set -XDeriveFunctor -XScopedTypeVariables
-- >>> import Control.Monad (void)
-- >>> import Data.Char (toUpper)

type family Base t :: * -> *

class Functor (Base t) => Recursive t where
  project :: t -> Base t t
#ifdef HAS_GENERIC
  default project :: (Generic t, Generic (Base t t), GCoerce (Rep t) (Rep (Base t t))) => t -> Base t t
  project = to . gcoerce . from
#endif

  cata :: (Base t a -> a) -- ^ a (Base t)-algebra
       -> t               -- ^ fixed point
       -> a               -- ^ result
  cata f = c where c = f . fmap c . project

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

class Functor (Base t) => Corecursive t where
  embed :: Base t t -> t
#ifdef HAS_GENERIC
  default embed :: (Generic t, Generic (Base t t), GCoerce (Rep (Base t t)) (Rep t)) => Base t t -> t
  embed = to . gcoerce . from
#endif

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

hylo :: Functor f => (f b -> b) -> (a -> f a) -> a -> b
hylo f g = h where h = f . fmap h . g

fold :: Recursive t => (Base t a -> a) -> t -> a
fold = cata

unfold :: Corecursive t => (a -> Base t a) -> a -> t
unfold = ana

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
ghylo w m f g = extract . h . return where
  h = fmap f . w . fmap (duplicate . h . join) . m . liftM g
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

-- | Course-of-value iteration
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
