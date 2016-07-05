{-# LANGUAGE TemplateHaskell, KindSignatures, DeriveFunctor, TypeFamilies #-}
module Main where

import Data.Functor.Foldable
import Data.Functor.Foldable.TH

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
    print $ cata evalAlg expr1
    print $ cata evalAlg expr2

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
