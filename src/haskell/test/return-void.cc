#include <stdio.h>
#define printInt(i) (((void)printf("%d\n", i)))
#define printDouble(d) (((void)printf("%f\n", d)))

// Test case begins here:

void prant() {
  return printDouble(1.0);
  printDouble(0.0);
}

int main() {
  prant();
  return 0;
}
