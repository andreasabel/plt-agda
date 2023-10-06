#!/bin/sh

here=`pwd`
cd $HOME/plt/www/laborations/lab3/testsuite
./plt-test-lab3 --doubles $here
# ./plt-test-lab3-jvm-verify $here
# ./plt-test-lab3-jvm-verify $here $HOME/plt/www/laborations/lab2/testsuite/good/
# ./plt-test-lab3 $here $HOME/plt/www/laborations/lab2/testsuite/good/

# EOF
