#define N 10

struct A {
  int _x;
  A (int x): _x(x) {}
};


struct B: public A {
  int _y;
  B (int x, int y): A(x), _y(y) {}
};

struct C: public A {
  int _z;
  C (int x, int z): A(x), _z(z) {}
};


extern int nd ();
A* p[N];

void foo () {
  for (int i=0; i < N; i++) {
    if (nd ())
      p[i] = new B (3*i, 3*i);
    else
      p[i] = new C (5*i, 5*i);
  }
}

int main (int argc, char**argv) {
  foo ();
  B* q = (B *) p[2];
  return q->_y;
}

