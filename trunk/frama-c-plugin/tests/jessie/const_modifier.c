

#include <stdio.h>

void f(int *p) {
  *p=1234;
}

const int n = 5678;

int main() {
  f((int*)&n);
  printf("n = %d\n",n); 
}
