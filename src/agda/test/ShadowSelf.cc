int f (int f) {  // This shadowing is ok
  return 0;
}

int main () {
  return f(0);
} 
