## 5.0.2
* Support GHC-8.2.1
* Fix Template Haskell derivation with non-default type renamer.
* Add `Recursive` and `Corecursive Natural` instances, with `Base Natural = Maybe`.

## 5.0.1
* Add `Data.Functor.Foldable.TH` module, which provides derivation of base functors via Template Haskell.

## 5
* Renamed `Foldable` to `Recursive` and `Unfoldable` to `Corecursive`. With `Foldable` in `Prelude` in GHC 7.10+, having a needlessly conflicting name seemed silly.
* Add support for GHC-8.0.1
* Use `Eq1`, `Ord1`, `Show1`, `Read1` to derive `Fix`, `Nu` and `Mu` `Eq`, `Ord` `Show` and `Read` instances
* Remove `Prim` data family. `ListF` as a new name for `Prim [a]`, with plenty of instances, e.g. `Traversable`.
* Export `unfix`
* Add chronomorphisms: `chrono` and `gchrono`.
* Add `distGApoT`

## 4.1.2
* Support for `free` 4.12.1

## 4.1.1
* Support for GHC 7.10
* Fixed `para`.

## 4.1
* Support for GHC 7.7+'s generalized `Typeable`.
* Faster `gapo` and `para` by exploiting sharing.

## 4.0

* Compatibility with `comonad` and `free` version 4.0

## 3.0

* Compatibility with `transformers` 0.3
* Resolved deprecation warnings caused by changes to `Data.Typeable`
