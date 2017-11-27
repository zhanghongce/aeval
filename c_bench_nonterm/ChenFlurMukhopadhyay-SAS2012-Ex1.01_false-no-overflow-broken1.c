extern int __VERIFIER_nondet_int(void);

int main() {
  int x, y;
  x = __VERIFIER_nondet_int();
  y = __VERIFIER_nondet_int();
  
  while (x + y > 0) {
    x = -6*x + 13;
  }
  return 0;
}
