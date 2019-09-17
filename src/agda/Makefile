# Makefile for PLT lab 2

agda=agda
agdafiles=Library.agda ../haskell/CPP/AST.agda ../haskell/CPP/Parser.agda WellTypedSyntax.agda TypeChecker.agda Value.agda Evaluation.agda Interpreter.agda FlowChart.agda
ghcflags=--ghc-flag=-i../haskell --ghc-flag=-Wwarn

.PHONY : test test-local

# Must be first goal...

lab2 : lab2.agda $(agdafiles)
	$(agda) --compile $(ghcflags) $<

# Otherwise infinite loop here...

test : lab2
	./run-testsuite.sh


test-local : lab2
	-./lab2 test/EqVoid.cc
	@echo "EXPECTED: syntax error"
	@echo "==========================================================================="
	-./lab2 test/ShadowFun.cc
	@echo "EXPECTED: type error"
	@echo "==========================================================================="
	-./lab2 test/ShadowParameter.cc
	@echo "EXPECTED: type error"
	@echo "==========================================================================="
	./lab2 test/print42.cc
	@echo "EXPECTED: success"
	@echo "==========================================================================="
	./lab2 test/AssignMany.cc
	@echo "EXPECTED: 12"

#EOF
