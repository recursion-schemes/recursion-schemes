## 5
* Renamed `Foldable` to `Recursive` and `Unfoldable` to `Corecursive`. With `Foldable` in `Prelude` in GHC 7.10+, having a needlessly conflicting name seemed silly.

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
