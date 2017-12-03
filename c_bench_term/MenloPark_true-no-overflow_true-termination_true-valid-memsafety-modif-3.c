extern int __VERIFIER_nondet_int(void);

int main()
{
  int x, y, z;
  x = __VERIFIER_nondet_int();
  y = __VERIFIER_nondet_int();
  if (y <= 1) return 0;
  z = 0;
  while (x > 0) {
    x = x - y;
    y = y - z;
    if (z == 1) z = -1; else z++;
  }
  return 0;
}
