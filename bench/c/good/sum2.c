



/* on veut sum(t,i,j) = t[i]+...+t[j-1] */

/*@ logic int sum(int[] t,int i,int j) 
  reads i,j,t,t[*] 
*/

/*@ axiom sum1 : 
      \forall int[] t, int i; sum(t,i,i) == 0 */
/*@ axiom sum2 : 
      \forall int[] t, int i, int j; sum(t,i,j+1) == sum(t,i,j) + t[j] */

/*@ requires \valid(t,0,n) (* t <> null and 0 <= offset(t) <= length(t)-n *)
  @ ensures \result == sum(t,0,n)
  @*/
int test1(int t[],int n) {
  int i,s = 0;
  /*@ invariant 0 <= i <= n && s == sum(t,0,i)
    @ variant n-i
    @*/
  for(i=0; i < n; i++) 
  {
    s = s + t[i];
  }
  return s;
}

/*@ requires \valid(t,0,n)
  @ assigns t[*]
  @ ensures sum(t,0,n) == \old(sum(t,0,n))+n
  @*/
void test2(int t[],int n) {
  int i;
 L:
  /*@ invariant 0 <= i <= n && 
         sum(t,0,n) == \at(sum(t,0,n),L)+i
    @ variant n-i
    @*/
  for(i=0; i < n; i++) 
  {
    t[i] = t[i] + 1;
  }
}
