extern int __VERIFIER_nondet_int(void);

int main()
{
  int y = __VERIFIER_nondet_int();
  int x = y + 2;
  
  while (x != y)
  {
    x = x-3;
    y = y-1;
  }
}
