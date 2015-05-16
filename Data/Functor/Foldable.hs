{-# LANGUAGE CPP, TypeFamilies, Rank2Types, FlexibleContexts, FlexibleInstances, GADTs, StandaloneDeriving, UndecidableInstances #-}
#ifdef __GLASGOW_HASKELL__
#if MIN_VERSION_base(4,7,0)
{-# LANGUAGE DeriveDataTypeable #-}
#endif
#endif
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Functor.Foldable
-- Copyright   :  (C) 2008-2013 Edward Kmett
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
  -- * Fixed points
  , Fix(..)
  , Mu(..)
  , Nu(..)
  , Prim(..)
  -- * Folding
  , Foldable(..)
  -- ** Combinators
  , gapo
  , gcata
  , zygo
  , gzygo
  , histo
  , ghisto
  , futu
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
  , Unfoldable(..)
  -- ** Combinators
  , gana
  -- ** Distributive laws
  , distAna
  , distApo
  , distGApo
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
import Control.Comonad.Trans.Class
import Control.Comonad.Trans.Env
import qualified Control.Comonad.Cofree as Cofree
import Control.Comonad.Cofree (Cofree(..))
import Control.Monad (liftM, join)
import Control.Monad.Free hiding (unfold)
import Data.Functor.Identity
import Control.Arrow
import Data.Function (on)
import Text.Read
#ifdef __GLASGOW_HASKELL__
import Data.Data hiding (gunfold)
#if MIN_VERSION_base(4,7,0)
#else
import qualified Data.Data as Data
#endif
#if MIN_VERSION_base(4,8,0)
import Prelude hiding (Foldable)
#endif
#endif

type family Base t :: * -> *

data family Prim t :: * -> *
-- type instance Base (Maybe a) = Const (Maybe a)
-- type instance Base (Either a b) = Const (Either a b)

class Functor (Base t) => Foldable t where
  project :: t -> Base t t

  cata :: (Base t a -> a) -- ^ a (Base t)-algebra
       -> t               -- ^ fixed point
       -> a               -- ^ result
  cata f = c where c = f . fmap c . project

  para :: (Base t (t, a) -> a) -> t -> a
  para t = p where p x = t . fmap ((,) <*> p) $ project x

  gpara :: (Unfoldable t, Comonad w) => (forall b. Base t (w b) -> w (Base t b)) -> (Base t (EnvT t w a) -> a) -> t -> a
  gpara t = gzygo embed t

  -- | Fokkinga's prepromorphism
  prepro
    :: Unfoldable t
    => (forall b. Base t b -> Base t b)
    -> (Base t a -> a)
    -> t
    -> a
  prepro e f = c where c = f . fmap (c . cata (embed . e)) . project

  --- | A generalized prepromorphism
  gprepro
    :: (Unfoldable t, Comonad w)
    => (forall b. Base t (w b) -> w (Base t b))
    -> (forall c. Base t c -> Base t c)
    -> (Base t (w a) -> a)
    -> t
    -> a
  gprepro k e f = extract . c where c = fmap f . k . fmap (duplicate . c . cata (embed . e)) . project

distPara :: Unfoldable t => Base t (t, a) -> (t, Base t a)
distPara = distZygo embed

distParaT :: (Unfoldable t, Comonad w) => (forall b. Base t (w b) -> w (Base t b)) -> Base t (EnvT t w a) -> EnvT t w (Base t a)
distParaT t = distZygoT embed t

class Functor (Base t) => Unfoldable t where
  embed :: Base t t -> t
  ana
    :: (a -> Base t a) -- ^ a (Base t)-coalgebra
    -> a               -- ^ seed
    -> t               -- ^ resulting fixed point
  ana g = a where a = embed . fmap a . g

  apo :: Foldable t => (a -> Base t (Either t a)) -> a -> t
  apo g = a where a = embed . (fmap (either id a)) . g

  -- | Fokkinga's postpromorphism
  postpro
    :: Foldable t
    => (forall b. Base t b -> Base t b) -- natural transformation
    -> (a -> Base t a)                  -- a (Base t)-coalgebra
    -> a                                -- seed
    -> t
  postpro e g = a where a = embed . fmap (ana (e . project) . a) . g

  -- | A generalized postpromorphism
  gpostpro
    :: (Foldable t, Monad m)
    => (forall b. m (Base t b) -> Base t (m b)) -- distributive law
    -> (forall c. Base t c -> Base t c)         -- natural transformation
    -> (a -> Base t (m a))                      -- a (Base t)-m-coalgebra
    -> a                                        -- seed
    -> t
  gpostpro k e g = a . return where a = embed . fmap (ana (e . project) . a . join) . k . liftM g

hylo :: Functor f => (f b -> b) -> (a -> f a) -> a -> b
hylo f g = h where h = f . fmap h . g

fold :: Foldable t => (Base t a -> a) -> t -> a
fold = cata

unfold :: Unfoldable t => (a -> Base t a) -> a -> t
unfold = ana

refold :: Functor f => (f b -> b) -> (a -> f a) -> a -> b
refold = hylo

data instance Prim [a] b = Cons a b | Nil deriving (Eq,Ord,Show,Read)
instance Functor (Prim [a]) where
  fmap f (Cons a b) = Cons a (f b)
  fmap _ Nil = Nil

type instance Base [a] = Prim [a]
instance Foldable [a] where
  project (x:xs) = Cons x xs
  project [] = Nil

  para f (x:xs) = f (Cons x (xs, para f xs))
  para f [] = f Nil

instance Unfoldable [a] where
  embed (Cons x xs) = x:xs
  embed Nil = []

  apo f a = case f a of
    Cons x (Left xs) -> x : xs
    Cons x (Right b) -> x : apo f b
    Nil -> []

-- | Example boring stub for non-recursive data types
type instance Base (Maybe a) = Const (Maybe a)
instance Foldable (Maybe a) where project = Const
instance Unfoldable (Maybe a) where embed = getConst

-- | Example boring stub for non-recursive data types
type instance Base (Either a b) = Const (Either a b)
instance Foldable (Either a b) where project = Const
instance Unfoldable (Either a b) where embed = getConst

-- | A generalized catamorphism
gfold, gcata
  :: (Foldable t, Comonad w)
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
  :: (Unfoldable t, Monad m)
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

futu :: Unfoldable t => (a -> Base t (Free (Base t) a)) -> a -> t
futu = gana distFutu

distFutu :: Functor f => Free f (f a) -> f (Free f a)
distFutu = distGFutu id

distGFutu :: (Functor f, Functor h) => (forall b. h (f b) -> f (h b)) -> Free h (f a) -> f (Free h a)
distGFutu _ (Pure fa) = Pure <$> fa
distGFutu k (Free as) = Free <$> k (distGFutu k <$> as)

newtype Fix f = Fix (f (Fix f))

unfix :: Fix f -> f (Fix f)
unfix (Fix f) = f

deriving instance Eq (f (Fix f)) => Eq (Fix f)
deriving instance Ord (f (Fix f)) => Ord (Fix f)
deriving instance Show (f (Fix f)) => Show (Fix f)
deriving instance Read (f (Fix f)) => Read (Fix f)

#ifdef __GLASGOW_HASKELL__
#if MIN_VERSION_base(4,7,0)
deriving instance Typeable Fix
#else
instance Typeable1 f => Typeable (Fix f) where
   typeOf t = mkTyConApp fixTyCon [typeOf1 (undefined `asArgsTypeOf` t)]
     where asArgsTypeOf :: f a -> Fix f -> f a
           asArgsTypeOf = const

fixTyCon :: TyCon
#endif
#if MIN_VERSION_base(4,7,0)
#else
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
instance Functor f => Foldable (Fix f) where
  project (Fix a) = a
instance Functor f => Unfoldable (Fix f) where
  embed = Fix

refix :: (Foldable s, Unfoldable t, Base s ~ Base t) => s -> t
refix = cata embed

toFix :: Foldable t => t -> Fix (Base t)
toFix = refix

fromFix :: Unfoldable t => Fix (Base t) -> t
fromFix = refix

-- | Lambek's lemma provides a default definition for 'project' in terms of 'cata' and 'embed'
lambek :: (Foldable t, Unfoldable t) => (t -> Base t t)
lambek = cata (fmap embed)

-- | The dual of Lambek's lemma, provides a default definition for 'embed' in terms of 'ana' and 'project'
colambek :: (Foldable t, Unfoldable t) => (Base t t -> t)
colambek = ana (fmap project)

newtype Mu f = Mu (forall a. (f a -> a) -> a)
type instance Base (Mu f) = f
instance Functor f => Foldable (Mu f) where
  project = lambek
  cata f (Mu g) = g f
instance Functor f => Unfoldable (Mu f) where
  embed m = Mu (\f -> f (fmap (fold f) m))

instance (Functor f, Eq (f (Fix f)), Eq (Fix f)) => Eq (Mu f) where
  (==) = (==) `on` toFix

instance (Functor f, Ord (f (Fix f)), Ord (Fix f)) => Ord (Mu f) where
  compare = compare `on` toFix

instance (Functor f, Show (f (Fix f)), Show (Fix f)) => Show (Mu f) where
  showsPrec d f = showParen (d > 10) $
    showString "fromFix " . showsPrec 11 (toFix f)

#ifdef __GLASGOW_HASKELL__
instance (Functor f, Read (f (Fix f)), Read (Fix f)) => Read (Mu f) where
  readPrec = parens $ prec 10 $ do
    Ident "fromFix" <- lexP
    fromFix <$> step readPrec
#endif

data Nu f where Nu :: (a -> f a) -> a -> Nu f
type instance Base (Nu f) = f
instance Functor f => Unfoldable (Nu f) where
  embed = colambek
  ana = Nu
instance Functor f => Foldable (Nu f) where
  project (Nu f a) = Nu f <$> f a

instance (Functor f, Eq (f (Fix f)), Eq (Fix f)) => Eq (Nu f) where
  (==) = (==) `on` toFix

instance (Functor f, Ord (f (Fix f)), Ord (Fix f)) => Ord (Nu f) where
  compare = compare `on` toFix

instance (Functor f, Show (f (Fix f)), Show (Fix f)) => Show (Nu f) where
  showsPrec d f = showParen (d > 10) $
    showString "fromFix " . showsPrec 11 (toFix f)

#ifdef __GLASGOW_HASKELL__
instance (Functor f, Read (f (Fix f)), Read (Fix f)) => Read (Nu f) where
  readPrec = parens $ prec 10 $ do
    Ident "fromFix" <- lexP
    fromFix <$> step readPrec
#endif

zygo :: Foldable t => (Base t b -> b) -> (Base t (b, a) -> a) -> t -> a
zygo f = gfold (distZygo f)

distZygo
  :: Functor f
  => (f b -> b)             -- An f-algebra
  -> (f (b, a) -> (b, f a)) -- ^ A distributive for semi-mutual recursion
distZygo g m = (g (fmap fst m), fmap snd m)

gzygo
  :: (Foldable t, Comonad w)
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

gapo :: Unfoldable t => (b -> Base t b) -> (a -> Base t (Either b a)) -> a -> t
gapo g = gunfold (distGApo g)

distApo :: Foldable t => Either t (Base t a) -> Base t (Either t a)
distApo = distGApo project

distGApo :: Functor f => (b -> f b) -> Either b (f a) -> f (Either b a)
distGApo f = either (fmap Left . f) (fmap Right)

-- | Course-of-value iteration
histo :: Foldable t => (Base t (Cofree (Base t) a) -> a) -> t -> a
histo = gcata distHisto

ghisto :: (Foldable t, Functor h) => (forall b. Base t (h b) -> h (Base t b)) -> (Base t (Cofree h a) -> a) -> t -> a
ghisto g = gcata (distGHisto g)

distHisto :: Functor f => f (Cofree f a) -> Cofree f (f a)
distHisto = distGHisto id

distGHisto :: (Functor f, Functor h) => (forall b. f (h b) -> h (f b)) -> f (Cofree h a) -> Cofree h (f a)
distGHisto k = Cofree.unfold (\as -> (extract <$> as, k (Cofree.unwrap <$> as)))

-- TODO: futu & chrono, these require Free monads
-- TODO: distGApoT, requires EitherT

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
  :: (Unfoldable t, Foldable t)
  => (Base t b -> b)
  -> (forall c. Base t c -> Base t c)
  -> (Base t (EnvT b (Cofree (Base t)) a) -> a)
  -> t
  -> a
zygoHistoPrepro f g t = gprepro (distZygoT f distHisto) g t
