{-# LANGUAGE CPP #-}
#if HAVE_QUANTIFIED_CONSTRAINTS
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE QuantifiedConstraints #-}

import Control.Applicative
import Data.Proxy
import Test.QuickCheck
import Test.QuickCheck.Classes

import Data.Bitraversable
import Data.Functor.Base
import Data.Functor.Foldable

instance Arbitrary2 TreeF where
  liftArbitrary2 arbA arbB = liftA2 NodeF arbA (listOf arbB)
instance Arbitrary a => Arbitrary1 (TreeF a) where
  liftArbitrary = liftArbitrary2 arbitrary
instance (Arbitrary a, Arbitrary b) => Arbitrary (TreeF a b) where
  arbitrary = arbitrary2

instance Arbitrary2 ListF where
  liftArbitrary2 arbA arbB =
    frequency [(1, return Nil), (3, liftA2 Cons arbA arbB)]
instance Arbitrary a => Arbitrary1 (ListF a) where
  liftArbitrary = liftArbitrary2 arbitrary
instance (Arbitrary a, Arbitrary b) => Arbitrary (ListF a b) where
  arbitrary = arbitrary2

instance Arbitrary2 NonEmptyF where
  liftArbitrary2 arbA arbB = liftA2 NonEmptyF arbA (liftArbitrary arbB)
instance Arbitrary a => Arbitrary1 (NonEmptyF a) where
  liftArbitrary = liftArbitrary2 arbitrary
instance (Arbitrary a, Arbitrary b) => Arbitrary (NonEmptyF a b) where
  arbitrary = arbitrary2

main :: IO ()
main = lawsCheckMany
  [ ("TreeF Int Int", laws0 (Proxy :: Proxy (TreeF Int Int)))
  , ("TreeF Int", laws1 (Proxy :: Proxy (TreeF Int)))
  , ("TreeF", laws2 (Proxy :: Proxy TreeF))
  , ("ListF Int Int", laws0 (Proxy :: Proxy (ListF Int Int)))
  , ("ListF Int", laws1 (Proxy :: Proxy (ListF Int)))
  , ("ListF", laws2 (Proxy :: Proxy ListF))
  , ("NonEmptyF Int Int", laws0 (Proxy :: Proxy (NonEmptyF Int Int)))
  , ("NonEmptyF Int", laws1 (Proxy :: Proxy (NonEmptyF Int)))
  , ("NonEmptyF", laws2 (Proxy :: Proxy NonEmptyF))
  ]

laws0 :: (Arbitrary p, Ord p, Show p, Read p) => Proxy p -> [Laws]
laws0 p = ($ p) <$>
  [ eqLaws
  , ordLaws
  , showLaws
  , showReadLaws
  ]

laws1 ::
  (Traversable f, forall a. Eq a => Eq (f a), forall a. Show a => Show (f a), forall a. Arbitrary a => Arbitrary (f a))
   => Proxy f -> [Laws]
laws1 p = ($ p) <$>
  [ functorLaws
  , foldableLaws
  , traversableLaws
  ]

laws2 ::
  (Bitraversable f, forall a b. (Eq a, Eq b) => Eq (f a b), forall a b. (Show a, Show b) => Show (f a b), forall a b. (Arbitrary a, Arbitrary b) => Arbitrary (f a b))
   => Proxy f -> [Laws]
laws2 p = ($ p) <$>
  [ bifunctorLaws
  , bifoldableLaws
  , bitraversableLaws
  ]

#else
main :: IO ()
main = putStrLn "Can't test laws for this version of GHC"
#endif
