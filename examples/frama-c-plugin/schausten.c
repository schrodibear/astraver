#include <stdlib.h>

/*@ requires \valid(p);
  @ ensures (\old(*p) < *p);
*/
void fun(int* p) {
  (*p)++;
}



int main() {
  fun(NULL);
  return 0;
}
