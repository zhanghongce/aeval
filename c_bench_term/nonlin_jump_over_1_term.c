extern int __VERIFIER_nondet_int(void);

int main() {
  int x = __VERIFIER_nondet_int();
  int y = __VERIFIER_nondet_int();
  
  if (x <= 2*y) return 0;
  
  while (x != 2*y) {
    if (x % y == 1) x++;
      else x = x - 2;
  }
  return 0;
}
