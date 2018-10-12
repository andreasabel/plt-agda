void f () { return; }

/* Trigggers error: invalid operands to binary expression ('void' and 'void') */
int main() {
  if (f() == f()) return 0;
  else return 1;
}
