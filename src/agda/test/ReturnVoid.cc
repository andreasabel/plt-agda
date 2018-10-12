#include "/Users/abel/plt/www/laborations/lab2/testsuite/prelude.cc"

void printFive () {
  return printInt(5);  // This is legal!
}

int main() {
  printFive();
}
 
