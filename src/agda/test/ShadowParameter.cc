// Shadowing of parameter by local in base block.

int main (int n) {
  int n = n + 1;  // this shadowing is illegal
  return n;
}

// Should give TYPE ERROR.
