.PHONY: all build test examples doctest ghcid

all : build

build :
	cabal v2-build --enable-tests

test : examples doctest

examples :
	cabal v2-test

doctest :
	cabal v2-exec -- doctest -DCURRENT_PACKAGE_KEY='"recursion-schemes"' -this-unit-id recursion-schemes -Iinclude src

ghcid :
	ghcid -c 'cabal v2-repl'
