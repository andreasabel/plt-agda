# Makefile for Agda implementation of PLT labs 2 & 3

agda=agda
agdafiles=\
  Library.agda \
  ../haskell/CPP/AST.agda \
  ../haskell/CPP/Parser.agda \
  WellTypedSyntax.agda \
  TypeChecker.agda \
  Value.agda \
  Evaluation.agda \
  Interpreter.agda \
  Compiler/FlowChart.agda \
  Compiler/BasicBlocks.agda \
  Compiler/BB/ToJasmin.agda

ghcflags=--ghc-flag=-i../haskell --ghc-flag=-Wwarn

.PHONY : test test-local lab2 lab3

# Must be first goal...

default : lab3

all : lab2 lab3

lab3 : lab3.agda $(agdafiles)
	$(agda) --compile $(ghcflags) $<

lab2 : lab2.agda $(agdafiles)
	$(agda) --compile $(ghcflags) $<

# Otherwise infinite loop here...

test : lab3
	./run-testsuite3.sh

test2 : lab2
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
