all : build

build :
	cabal v2-build --enable-tests

doctest :
	doctest -DCURRENT_PACKAGE_KEY='"recursion-schemes"' -this-unit-id recursion-schemes -Iinclude src

ghcid :
	ghcid -c 'cabal v2-repl'
