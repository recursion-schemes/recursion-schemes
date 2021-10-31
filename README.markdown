# recursion-schemes

[![Hackage](https://img.shields.io/hackage/v/recursion-schemes.svg)](https://hackage.haskell.org/package/recursion-schemes) [![Build Status](https://github.com/ekmett/recursion-schemes/workflows/Haskell-CI/badge.svg)](https://github.com/ekmett/recursion-schemes/actions?query=workflow%3AHaskell-CI)

This package represents common recursion patterns as higher-order functions.

## A familiar example

Here are two recursive functions.

```haskell
sum :: [Int] -> Int
sum [] = 0
sum (x:xs) = x + sum xs

product :: [Int] -> Int
product [] = 1
product (x:xs) = x * product xs
```

These functions are very similar. In both cases, the empty list is the base case. In the cons case, each makes a recursive call on the tail of the list. Then, the head of the list is combined with the result using a binary function.

We can abstract over those similarities using a higher-order function, [`foldr`](https://hackage.haskell.org/package/base/docs/Data-List.html#v:foldr):

```haskell
sum     = foldr (+) 0
product = foldr (*) 1
```

## Other recursive types

`foldr` works great for lists. The higher-order functions provided by this library help with other recursive datatypes. Here are two recursive functions on [`Tree`s](https://hackage.haskell.org/package/containers/docs/Data-Tree.html#t:Tree):

```haskell
depth :: Tree a -> Int
depth (Node _ subTrees) = 1 + maximum subTrees

size :: Tree a -> Int
size (Node _ subTrees) = 1 + sum subTrees
```

It is not possible to use `foldr` to simplify `depth`. Conceptually, `foldr` is flattening all the elements of the tree into a list before combining them with the binary function. This does not work for `depth` because it needs to examine the structure of the tree, which `foldr` flattened away.

We can instead use one of the higher-order functions provided by this library, [`cata`](https://hackage.haskell.org/package/recursion-schemes/docs/Data-Functor-Foldable.html#v:cata).

```haskell
import Data.Functor.Base (TreeF(..))
import Data.Functor.Foldable

-- data Tree  a   = Node  a [Tree a]
-- data TreeF a r = NodeF a [r     ]

depth :: Tree a -> Int
depth = cata go
  where
    go :: TreeF a Int -> Int
    go (NodeF _ subDepths) = 1 + maximum subDepths

size :: Tree a -> Int
size = cata go
  where
    go :: TreeF a Int -> Int
    go (NodeF _ subSizes) = 1 + sum subSizes
```

In this example, the code is a bit longer, but it is correct. Did you spot the mistake in the version which does not use `cata`? We forgot a call to `fmap`:

```haskell
depth :: Tree a -> Int
depth (Node _ subTrees) = 1 + maximum (fmap depth subTrees)

size :: Tree a -> Int
size (Node _ subTrees) = 1 + sum (fmap size subTrees)
```

`cata` automatically adds this call to `fmap`. This is why `subDepths` contains a list of already-computed depths, not a list of sub-trees. In general, each recursive position is replaced by the result of a recursive call. These results have type `Int`, not type `Tree`, so we need a helper datatype `TreeF` to collect these results.

When you think about computing the depth, you probably think "it's 1 plus the maximum of the sub-depths". With `cata`, this is exactly what we write. By contrast, without `cata`, we need to describe both the "how" and the "what" in our implementation. The "how" is about recurring over the sub-trees (using `fmap depth`), while the "what" is about adding 1 to the maximum of the sub-trees. `cata` takes care of the recursion, so you can focus solely on the "what".

A **recursion-scheme** is a function like `cata` which implements a common recursion pattern. It is a higher-order recursive function which takes a non-recursive function as an argument. That non-recursive function describes the part which is unique to your calculation: the "what".

## Types with many constructors

Let's look at a more complex example. Here is a small lambda-calculus and a function to compute the [free variables](https://en.wikipedia.org/wiki/Lambda_calculus#Free_variables) of an expression:

```haskell
import Data.Set (Set)
import qualified Data.Set as Set

data Expr
  = Var String
  | Lam String Expr
  | App Expr Expr
  | Constant Int
  | Add Expr Expr
  | Sub Expr Expr
  | Mul Expr Expr
  | Div Expr Expr
  | ...

freeVars :: Expr -> Set String
freeVars (Var name)      = Set.singleton name
freeVars (Lam name body) = Set.difference (freeVars body) (Set.singleton name)
freeVars (App e1 e2)     = Set.union (freeVars e1) (freeVars e2)
freeVars (Constant _)    = Set.empty
freeVars (Add e1 e2)     = Set.union (freeVars e1) (freeVars e2)
freeVars (Sub e1 e2)     = Set.union (freeVars e1) (freeVars e2)
freeVars (Mul e1 e2)     = Set.union (freeVars e1) (freeVars e2)
freeVars (Div e1 e2)     = Set.union (freeVars e1) (freeVars e2)
freeVars ...
```

As you can see, we had to repeat the `Set.union (freeVars e1) (freeVars e2)` line over and over. With recursion-schemes, this code becomes much shorter:

```haskell
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, TemplateHaskell, TypeFamilies #-}
import Data.Functor.Foldable.TH (makeBaseFunctor)

makeBaseFunctor ''Expr

freeVars :: Expr -> Set String
freeVars = cata go
  where
    go :: ExprF (Set String) -> Set String
    go (VarF name)           = Set.singleton name
    go (LamF name bodyNames) = Set.difference bodyNames (Set.singleton name)
    go fNames                = foldr Set.union Set.empty fNames
```

The `makeBaseFunctor` line uses Template Haskell to generate our `ExprF` datatype, a single layer of the `Expr` datatype. `makeBaseFunctor` also generates instances which are useful when using recursion-schemes. For example, we make use of the `Foldable ExprF` instance on the last line of `go`. This `Foldable` instance exists because `ExprF` has kind `* -> *`, while `Expr` has kind `*`.

## Other recursion-schemes

All of our examples so far have used `cata`. There are many more recursion-schemes. Here is an example which follows a different recursive structure:

```haskell
-- |
-- >>> halves 256
-- [256,128,64,32,16,8,4,2,1]
halves :: Int -> [Int]
halves 0 = []
halves n = n : halves (n `div` 2)
```

That recursive structure is captured by the [`ana`](https://hackage.haskell.org/package/recursion-schemes/docs/Data-Functor-Foldable.html#v:ana) recursion-scheme:

```haskell
halves :: Int -> [Int]
halves = ana go
  where
    go :: Int -> ListF Int Int
    go 0 = Nil
    go n = Cons n (n `div` 2)
```

The [Data.Functor.Foldable](https://hackage.haskell.org/package/recursion-schemes/docs/Data-Functor-Foldable.html) module provides many more.

## Flowchart for choosing a recursion-scheme

![](./docs/flowchart.svg)
![](./docs/docs/flowchart.svg)

In addition to the choices described by the flowchart, you can always choose to use a refold.

## Contributing

Contributions and [bug reports](https://github.com/ekmett/recursion-schemes/issues/new) are welcome!
