.PHONY: all build test examples docspec ghcid

all : build

build :
	cabal v2-build --enable-tests

test : examples docspec

examples :
	cabal v2-test

# https://github.com/phadej/cabal-extras/tree/master/cabal-docspec
docspec :
	cabal-docspec

ghcid :
	ghcid -c 'cabal v2-repl'
