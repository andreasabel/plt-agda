#include <stdio.h>
#define printInt(i) (printf("%d\n", i))

int main () {
  int y = 0;
  while (y++ < 1) int y = 0; // if the scope is wrong for while, this may loop!
  printInt(y); // should print 2 (condition is checked twice)
  return 0;
}
