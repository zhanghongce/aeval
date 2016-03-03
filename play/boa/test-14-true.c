struct foo {
  int x;
  int y;
}; 

struct foo gv_;
struct foo *gv = &gv_;

int main() {
  gv->y = 10; // (*gv).y = 10;
  return 0;
}
