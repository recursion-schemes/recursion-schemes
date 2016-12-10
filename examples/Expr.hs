{-# LANGUAGE TemplateHaskell, KindSignatures, DeriveTraversable, TypeFamilies #-}
module Main where

import Data.Functor.Foldable
import Data.Functor.Foldable.TH

import Test.HUnit

data Expr a
    = Lit a
    | Add (Expr a) (Expr a)
    | Mul (Expr a) (Expr a)
  deriving (Show)

makeBaseFunctor ''Expr

expr1 :: Expr Int
expr1 = Add (Lit 2) (Mul (Lit 3) (Lit 4))

main :: IO ()
main = do
    let expr2 = ana divCoalg 55 :: Expr Int
    14 @=? cata evalAlg expr1
    55 @=? cata evalAlg expr2

    -- assert expr1 evaluates to 14
    -- assert expr2 evaluates to 55, QuickCheck ?
  where
    evalAlg (LitF x)   = x
    evalAlg (AddF x y) = x + y
    evalAlg (MulF x y) = x * y

    divCoalg x
        | x < 5     = LitF x
        | even x    = MulF 2 x'
        | otherwise = AddF x' (x - x')
      where
        x' = x `div` 2
