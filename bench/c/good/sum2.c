



/* on veut sum(t,i,j) = t[i]+...+t[j-1] */

/* @ logic int sum(int[] t,int i,int j) */

/* @ axiom sum(t,i,i) == 0 */
/* @ axiom sum(t,i,j+1) == sum(t,i,j) + t[j] */



/* @ requires t != null && n <= \length(t);
  @ ensures \result == sum(t,0,n);
  @*/
int test(int t[],int n) {
  int i,s = 0;
  for(i=0; i < n; i++) 
    /* @ invariant 0 <= i <= n && s == sum(t,0,i);
      @ variant n-i;
      @*/
  {
    s /* += */ = s + t[i];
  }
  return s;
}
