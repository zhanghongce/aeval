#include <stddef.h>

int nd();

void test01(int *x, int i) {
    if (x == NULL) {
        i = 1; //inconsistent
        //int j = nd();
    }
    *x = i;
}


void test02(int *x, int i) {
    *x = i ;
    if (x== NULL) {
        i = 1; //inconsistent
        int j = nd();
    }
}
