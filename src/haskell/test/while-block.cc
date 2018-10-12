#include <stdio.h>
#define printInt(i) (printf("%d\n", i))

int main () {
  int i = 0;
  int result = 1;
  while (i < 9) {
    int prev;  // undefined value
    int tmp;   // undefined value
    if (i == 0) tmp = 1; else tmp = prev;  // tmp undefined if i>0
    prev = result;
    result = tmp + result;  // This may fail with "uninitialized variable"
    i++;
  }
  printInt(result); // This could print 89, but value of result is undefined.
  return 0;
}
