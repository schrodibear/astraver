



/* on veut sum(t,i,j) = t[i]+...+t[j-1] */

/* @ logic int sum(int[] t,int i,int j) 
  (* reads i,j,t,t[*] *)
*/

/*@ axiom sum1 : 
      \forall int[] t, int i; sum(t,i,i) == 0 */
/*@ axiom sum2 : 
      \forall int[] t, int i, int j; sum(t,i,j+1) == sum(t,i,j) + t[j] */

/*@ requires t != \null && n <= \length(t)
  @ (* modifiable \nothing *)
  @ ensures \result == sum(t,0,n)
  @*/
int test1(int t[],int n) {
  int i,s = 0;
  for(i=0; i < n; i++) 
    /* @ invariant 0 <= i <= n && s == sum(t,0,i)
      @ variant n-i
      @*/
  {
    s += t[i];
  }
  return s;
}

/* @ requires t != null && n <= \length(t)
  @ (* modifiable t[*] *)
  @ ensures sum(t,0,n) == \old(sum(t,0,n))+n
  @*/
void test2(int t[],int n) {
  int i;
  for(i=0; i < n; i++) 
    /* @ invariant 0 <= i <= n && sum(t,0,i) == \old(sum(t,0,i))+i
      @ variant n-i
      @*/
  {
    /* t[i]++ : invalid lvalue !! */
    t[i] = t[i] + 1;
  }
}
