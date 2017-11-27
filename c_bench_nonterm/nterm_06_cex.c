extern int __VERIFIER_nondet_int(void);

int main()
{
  int x = 0;
  int y = 0;
  while (x == y)
  {
    y = __VERIFIER_nondet_int();
    x = x + 1;
  }
}

