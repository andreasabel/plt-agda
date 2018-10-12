#include <stdio.h>
#define printInt(i) (printf("%d\n", i))

int main () {
  int y = 0;
  if (1 == 1) int y = 1; else int y = 2;
  printInt(y); // should print 0
  return y;
}
