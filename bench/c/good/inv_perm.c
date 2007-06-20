
/* Inverse of a permutation, in place.
   The Art of Computer Programming, vol. 1, page 176 */

/*@ requires 
  @   n >= 0 && \valid_range(t,1,n) &&
  @   \forall int k; 1 <= k <= n => 1 <= t[k] <= n
  @*/
void inverse(int *t, int n) {
  int m = n, j = -1;
  /*@ invariant 0 <= m <= n 
    @ variant m
    @*/
  while (m > 0) {
    int i = t[m];
    //@ label L
    /*@ invariant 1 <= m <= n && i == t[m]
      @*/
    while (i > 0) {
      t[m] = j;
      j = -m;
      m = i;
      i = t[m];
    }
    //@ assert m == \at(m,L)
    i = j;
    t[m] = -i;
    m--;
  }
}

/* test */

int n = 6;
int t[7] = { 0,2,3,1,6,5,4 };

void print(int *t, int n) {
  int i;
  for (i = 1; i <= n; i++) printf("%d ", t[i]);
  printf("\n");
}

int main() {
  print(t,n);
  inverse(t, n);
  print(t,n);
}

