// RUN: %sea pf -O0 --abc=%abc_encoding "%s" 2>&1 | OutputCheck %s
// CHECK: ^unsat$

#include <stdio.h>
int main(int argc, char**argv) 
{
  int i;
  int a[10];
  for (i = 0; i < 10; i++) 
  {
    a[i] = i;
  }
  printf("%d\n", a[i-1]);
  return 42;
}
