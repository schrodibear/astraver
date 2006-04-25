
int t[10];

/*@ assigns t[..]
    ensures \forall int k; 0 <= k < 10 => t[k] == 0 */
void f1() {
  int i;
  /*@ invariant 0 <= i <= 10 && \forall int k; 0 <= k < i => t[k] == 0
    @ loop_assigns t[..]
    @ variant 10-i
    @*/
  for (i = 0; i < 10; i++) t[i] = 0;
}

/*@ assigns t[0 .. 9]
    ensures \forall int k; 0 <= k < 10 => t[k] == 0 */
void f2() {
  int i;
  /*@ invariant 0 <= i <= 10 && \forall int k; 0 <= k < i => t[k] == 0
    @ loop_assigns t[0 .. 9]
    @ variant 10-i
    @*/
  for (i = 0; i < 10; i++) t[i] = 0;
}

