#include <stdio.h>
#define printInt(i) (printf("%d\n", i))

int main () {
  int i = 0;
  int result = 1;
  while (i < 9) {
    int prev;
    if (i == 0) prev = 1;
    { int tmp = result;
      result = result + prev;
      prev = tmp;
    }
    i++;
  }
  printInt(result); // should print 89
  return 0;
}
