# Makefile for PLT lab 2

# alex 3.2.6 does not produce GHC 9.2-compatible Haskell with option --ghc
# ALEX_OPTS=--ghc

.PHONY: test

all : lab2 test

test : test/dont-bind-too-eagerly.cc # scopes-reuse-name.cc # while-scope.cc  # if-scope.cc  # while-block.cc
	./lab2 $<

testsuite : lab2
	./run-testsuite.sh

lab2 : lab2.hs TypeChecker.hs Interpreter.hs CPP/Test
	ghc --make lab2.hs -o lab2

CPP/Test.hs CPP/Lex.x CPP/Par.y CPP/Abs.hs CPP/Print.hs CPP/AST.agda : CPP.cf Makefile
	bnfc --haskell --agda -d $<

CPP/Par.hs: CPP/Par.y
	happy -gcai $<

CPP/Lex.hs: CPP/Lex.x
	alex $(ALEX_OPTS) $<

CPP/Test: CPP/Test.hs CPP/Par.hs CPP/Lex.hs
	ghc --make $< -o $@

clean:
	-rm -f CPP/*.log CPP/*.aux CPP/*.hi CPP/*.o CPP/*.dvi

distclean: clean
	-rm -f CPP/Doc.* CPP/Lex.* CPP/Par.* CPP/Layout.* CPP/Skel.* CPP/Print.* CPP/Test.* CPP/Abs.* CPP/Test CPP/ErrM.* CPP/SharedString.* CPP/ComposOp.* CPP/CPP.dtd CPP/XML.*
	-rmdir -p CPP/

# EOF
