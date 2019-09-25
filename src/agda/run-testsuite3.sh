#!/bin/sh

here=`pwd`
cd $HOME/plt/www/laborations/lab3/testsuite
./progs-test-lab3 --doubles $here
# ./progs-test-lab3-jvm-verify $here
# ./progs-test-lab3-jvm-verify $here $HOME/plt/www/laborations/lab2/testsuite/good/
# ./progs-test-lab3 $here $HOME/plt/www/laborations/lab2/testsuite/good/

# EOF
