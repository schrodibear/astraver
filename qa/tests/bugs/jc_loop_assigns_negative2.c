/*@
  requires n > 0 && \valid(ar + (0 .. n - 1));
  assigns ar[0 .. n - 1];
  ensures \forall integer i; 0 <= i < n ==> ar[i] == i;
 */
void strange_loop(int *ar, int n) {
    ar[0] = 0;

    int i = 1;
    /*@
      loop invariant 1 <= i <= n;
      loop invariant \forall integer j; 1 <= j < i ==> ar[j] == j;

      loop assigns ar[1 .. i - 1];

      loop variant n - i;
     */
    while (i < n)
    /*@
      assigns ar[i], i;
      ensures \let o = \old(i); ar[o] == o;
      ensures i == \old(i) + 1;
     */
    {
        ar[i] = i;
        ++i;
    }
}