#include <stdlib.h>
#include <stdbool.h>
#include <stdio.h>
#include <assert.h>

typedef struct example_s {
	struct example_s* bases;
	const char* repr;
} example;

#define hashCode(this) ((size_t) this->bases)



bool example1(example* this, const example* other) {

	if (this->bases == NULL) {
		if (other->bases != NULL) {
			return false;
		} // here we know that this->base==other->base==NULL
	}

	if (hashCode(this->bases) != hashCode(other->bases)) { //inconsistent with 17
		return false;
	}

  return true;
}

int example2(int n) {
  int arr[n];
	arr[3] = 3;
	return arr[n]; // Inconsistent with 28
}

int example3(example* o) {
  if (o != NULL) {
	  return hashCode(o);
  }
	printf("%s does not exist\n", o->repr); //inconsistent with line 34
	return 2;
}

void example4(int n) {
	int arr[n];
	int i;
	for (i=0; i<=n; i++) {
	  arr[i]=i; // inconsistent off by one
  }
}

void example5(int a, int b) {
  b=1; // all inconsistent: div by zero
	if (a>0) b--;
  b=1/b;
	if (a<=0) b=1/(1-b);
}


bool example6(example* o) {
    printf("%s\n", o->repr);
	if (o == NULL) {
	  return false; // inconsistent wrt 57
	}
	return true;
}

int example7(int arr[]) {
	return arr[-1]; // inconsistent
}

void example8(int length) {
	char temp[length];
	int repos = -1;
	int end = -1;
	int j = end;
	do {
		j++;
                assert (j < length);
		if (temp[j]=='a') {
			repos = j - end - 1;
		}
	} while (repos == -1 && j < length);
	if (repos == -1) {
		repos=0; //unreachable
	}
}

int getInt(int n) {
	return 0;
}

int example9(int index, int ints_size, int chars_size, int bytes_size, int booleans_size) {
	int max = 0;
	if (booleans_size > 0 && index < 63)
		max = 64;
	else if (bytes_size > 0 && index < 56)
		max = 57;
	else if (chars_size > 0 && index < 48)
		max = 49;
	else if (ints_size > 0 && index < 32)
		max = 33;

	if (max != 0) {
		int rand = getInt(4);
		max = max - index;
		//at this point, max must be 1 because
		//if max!=0, then one of the cases above
		//was taken s.t. max is always set to index+1
		// hence the line above always sets index to 1
		if (max > rand)
			max = rand;
		else if (max != 1)
			max = getInt(max); // unreachable
		index+=max;
	}
	return index;
}
//
// extern example* nd_example_tr ();
// extern const example* nd_example_tr_2 ();
// extern int nd_int ();
// extern void* nd_ptr ();
//
// int main() {
// 	printf("Hello world\n");
// 	bool ex1 = 	example1(nd_example_tr (), nd_example_tr_2 ());
// }
