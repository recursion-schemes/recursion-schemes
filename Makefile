all : build

build :
	cabal new-build --enable-tests

doctest :
	doctest -DCURRENT_PACKAGE_KEY='"recursion-schemes"' -Iinclude src

ghcid :
	ghcid -c 'cabal new-repl'
