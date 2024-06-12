## next [????-??-??]

* Support GHC-9.10.
* Drop support for GHC-7.10 and earlier.

## 5.2.2.5 [2023-10-14]

* Support GHC-9.6 and GHC-9.8
* Support `th-abstraction-0.6.0.0` or later.

## 5.2.2.4 [2023-02-27]

* Support `th-abstraction-0.5.0.0` or later.

## 5.2.2.3

* Support GHC-9.4
* Workaround for https://gitlab.haskell.org/ghc/ghc/-/issues/18320, which was
  preventing code calling makeBaseFunctor from being profiled.

## 5.2.2.2

* Support GHC-9.0 and GHC-9.2

## 5.2.2.1

* Fix build issue regarding `Setup.hs`. See #120.

## 5.2.2
* More Mendler-style recursion-schemes: `mpara`, `mzygo`, `mana`, `mapo`, and
  `mfutu`.
* `makeBaseFunctor` no longer generates warnings when combined with
  DerivingStrategies.

## 5.2.1 [2020-10-04]
* Allow building with `template-haskell-2.17.0.0` (GHC 9.0).

## 5.2

* Add instances for `Tree` (from `containers`)
* Add some haddocks and basic examples
* Generalize the type of `makeBaseFunctor(With)`, such that
  it can take also `Dec`. This way you may supply context for `Recursive`
  and `Corecursive` instances.
* Depend on `data-fix` package for fixed point types.

## 5.1.3 [2019-04-26]
* Support `th-abstraction-0.3.0.0` or later.

## 5.1.2
* Make the `Generic`-based instances to also support data constructors with zero
  arguments (and datatypes with zero constructors).

## 5.1.1.1

* Invalid release

## 5.1.1

* Add `cotransverse`
* Add `Generic` based default implementation to `embed` and `project`.
  `Recursive` and `Corecursive` can be `DeriveAnyClass`-derived now,
  if you write the base functor by hand.

## 5.1
* Export gfutu
* `distGHisto`, `ghisto`, and `gchrono` now use `Cofree (Base t)`
* `distGFutu`, `gfutu`, and `gchrono` now use `Free (Base t)`
* Add `hoist`, `hoistMu` and `hoistNu`
* Add `transverse` and `cataA`

## 5.0.3 [2018-07-01]
* Make the Template Haskell machinery look through type synonyms.
* Avoid incurring some dependencies when using recent GHCs.

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
