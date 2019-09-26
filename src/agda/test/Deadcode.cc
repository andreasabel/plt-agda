// Only dead code
#define printInt(i) printf("%d",i)
int main () {
  int i;
  if (false && i > 0) printInt(i); else {}
  if (false && i > 0 || false && i < 1) printInt(i); // creates a dead block
  else 1 + 2 * 3 - 4 + 1;
  return 1;
}
