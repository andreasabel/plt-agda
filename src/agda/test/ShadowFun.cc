// A function shadowed by a parameter cannot be called.

int x (int n) {
  if (n <= 0) return 1;
  else {
    // shadow the function, this this legal
    int x = n-1;
    // function is shadowed and cannot be called!
    return x(x) * x;
  }
}

int main() {
  return(x(7));
}

// Should fail.
