
#include <stdio.h>

struct A {
    int x;
    int y;
};
struct B {
    struct A a;
    int z;
};

typedef int arr3[3];

void f(arr3 t, struct B b) {
  printf("sizeof(int): %ld\n",sizeof(int));
  printf("sizeof(void*): %ld\n",sizeof(void*));
  printf("sizeof(t): %ld\n",sizeof(t));
  printf("sizeof(b): %ld\n",sizeof(b));
  printf("sizeof(*t): %ld\n",sizeof(*t));
}

int main() {
  arr3 t;
  struct B b;
  f(t,b);
  return 0;
}


