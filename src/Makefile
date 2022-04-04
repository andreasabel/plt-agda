build:
	make -C agda all
	hpack
	cabal build

all:
	make -C haskell
	make -C agda all

# EOF
