/*@
  requires n > 0;
  assigns \nothing;
 */
void strange_loop(int n) {
    int *ar = malloc(sizeof(*ar) * n);
    int i = 0;
    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer j; 0 <= j < i ==> ar[j] == j;

      loop assigns ar[1 .. i];

      loop variant n - i;
     */
    while (i < n) {
        ar[i] = i;
        ++i;
    }
}
