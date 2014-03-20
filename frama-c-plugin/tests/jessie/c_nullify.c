#include <limits.h>

/*@
  requires n < UINT_MAX;
  requires \valid(a+(0..n-1));
  assigns a[0..n-1];
*/
void C_nullify(char* a, unsigned int n)
{
  unsigned int i;
  if (n == 0) return;

  /*@
     loop invariant \forall integer k; 0<=k<i ==> a[k] == 0;
     loop assigns i,a[0..n-1];
     loop variant n - i;
  */
  for (i = 0; i < n; i++) {
    a[i] = 0;
  }  
}

int main()
{
  char arr[10];
  C_nullify(arr, 10);
  return 0;
}
