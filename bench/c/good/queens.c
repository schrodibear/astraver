/****
t(a,b,c){int d=0,e=a&~b&~c,f=1;if(a)for(f=0;d=(e-=d)&-e;f+=t(a-d,(b+d)*2,(
c+d)/2));return f;}main(q){scanf("%d",&q);printf("%d\n",t(~(~0<<q),0,0));}
****/


//@ logic int bit(int x, int i)

//@ logic int nbits(int x)

//@ axiom nbits_nonneg : \forall int x; nbits(x) >= 0

//@ axiom nbits_zero : \forall int x; nbits(x)==0 <=> x==0

//@ logic int lowest_bit(int x)

/*@ axiom lowest_bit_def : 
  @   \forall int x; x != 0 => 
  @     \exists int i; (i >= 0 && 
  @                     lowest_bit(x) == bit(x,i) &&
  @                     bit(x,i) != 0 &&
  @                     \forall int j; 0 <= j < i => bit(x,j) == 0)
  @*/

/*@ axiom lowest_bit_zero :
  @   \forall int x; lowest_bit(x) == 0 <=> x == 0
  @*/

/*@ axiom lowest_bit_trick :
  @   \forall int x; x & -x == lowest_bit(x)
  @*/

/*@ axiom remove_one_bit :
  @    \forall int x, int i; 
  @       bit(x,i) != 0 => nbits(x - bit(x,i)) == nbits(x) - 1
  @*/

// count_bits as a warmup...
/*@ ensures \result == nbits(x) */
int count_bits(int x) {
  int d = 0, c = 0;
  /*@ invariant c + nbits(x-d) == nbits(\at(x,init))
    @ variant   nbits(x-d)
    @*/
  while (d = (x-=d) & -x) c++;
  return c;
}

/* integers as sets of bits */

/*@ predicate b_in(int i, int x) { bit(x,i) != 0 } */

/*@ axiom bwand_set : \forall int x, int y; 
  @   \forall int i; b_in(i,x&y) <=> (b_in(i,x) && b_in(i,y)) 
  @*/

/*@ predicate included(int x, int y) { 
  @   \forall int i; b_in(i,x) => b_in(i,y) 
  @ } 
  @*/

/*@ axiom included_trans : \forall int x, int y, int z;
  @   included(x,y) => included(y,z) => included(x,z)
  @*/

/*@ axiom included_bwand_l : \forall int x, int y; included(x&y, x) */

/*@ axiom included_bwand_r : \forall int x, int y; included(x&y, y) */

/*@ axiom included_sub : \forall int x, int y;
  @   included(x,y) => included(y-x, y)
  @*/

/*@ axiom included_nbits : \forall int x, int y;
  @   included(x,y) => nbits(y-x) == nbits(y) - nbits(x)
  @*/

/*@ axiom included_lowest_bit : \forall int x; included(lowest_bit(x), x) */

/*@ logic int singleton(int i) */ // this is 2^i

/*@ axiom singleton_def : \forall int i, int j; b_in(j,singleton(i)) <=> j==i
  @*/

/*@ axiom lowest_bit_is_singleton : \forall int x;
  @   x != 0 => \exists int i; lowest_bit(x) == singleton(i)
  @*/

/*@ logic int all_ones(int n) */ // this is 2^n-1, that 11...1 with n ones

/*@ axiom all_ones_def : \forall int n; 
  @   \forall int i; b_in(i, all_ones(n)) => 0 <= i < n
  @*/   

/* @ axiom help_1: \forall int a, int n, int i;
  @   b_in(i,a) => included(a,all_ones(n)) => 0 <= i < n
  @*/

//@ axiom all_ones_trick : \forall int n; ~(~0<<n) == all_ones(n)

//@ axiom nbits_all_ones : \forall int n; nbits(all_ones(n))==n


// t1: termination of the for loop
int t1(int a, int b, int c){
  int d=0, e=a&~b&~c, f=1;
  if (a)
    /*@ variant nbits(e-d) */
    for (f=0; d=(e-=d)&-e; ) {
      f+=t1(a-d,(b+d)*2,(c+d)/2);
    }
  return f;
}

// t2: termination of the for loop: nbits(a) decreases
int t2(int a, int b, int c){
  int d=0, e=a&~b&~c, f=1;
  // @ assert included(e,a)
  //@ label L
  if (a)
    /*@ invariant included(d,e) && included(e,\at(e,L)) */
    for (f=0; d=(e-=d)&-e; ) {
      // @ assert d == lowest_bit(e)
      // @ assert included(d,e)
      //@ assert nbits(a-d) < nbits(a)
      f+=t2(a-d,(b+d)*2,(c+d)/2);
    }
  return f;
}

// soundess: every recorded solution is indeed a solution

//@ logic int N() (* N queens on a NxN chessboard *)
//@ axiom N_positive : N() > 0

int** sol; // sol[i] is the i-th solution
/*@ axiom dont_bother_me_I_am_a_ghost_1 : 
  @   \forall int i; \valid(sol+i) */
/*@ axiom dont_bother_me_I_am_a_ghost_2 : 
  @   \forall int i, int j; \valid(sol[i]+j) */

int s = 0; // next empty slot for a solution

int *col; // current solution being built
int k;    // current row in the current solution

// s stores a partial solution, for the rows 0..k-1
/*@ predicate partial_solution(int k, int* s) {
  @   \forall int i; 0 <= i < k => 
  @      (\exists int j; 0 <= j < N() && s[i] == singleton(j)) (* &&
  @      (\forall int j; j > i => ((s[i] >> (j-i)) != s[j] &&
  @                                (s[i] << (j-i)) != s[j])) *)
  @ }
  @*/

/*@ predicate solution(int *s) { partial_solution(N(), s) } */

/*@ requires solution(col)
  @ assigns  s, sol[s][0..N()-1]
  @ ensures  s==\old(s)+1 && \forall int i; sol[\old(s)][i]==col[i]
  @*/
void store_solution();

/*@ requires
  @   k >= 0 && nbits(a) + k == N() &&
  @   included(a,all_ones(N())) && 
  @   s >= 0 && partial_solution(k, col)
  @ assigns
  @   col[k..], s, k, sol[s..][..]
  @ ensures  
  @   \result == s - \old(s) && \result >= 0 &&
  @   k == \old(k)
  @*/
int t3(int a, int b, int c){
  int d=0, e=a&~b&~c, f=1;
  //@ label L
  if (a)
    /*@ invariant 
      @   included(d,e) && included(e,\at(e,L)) &&
      @   f == s - \at(s,init) && f >= 0 &&
      @   k == \old(k) && partial_solution(k, col)
      @ loop_assigns
      @   col[k..], s, k, sol[s..][..]
      @*/
    for (f=0; d=(e-=d)&-e; ) {
      //@ assert included(d,e)
      //@ assert \exists int i; d == singleton(i) && b_in(i,a) && 0 <= i < N()
      col[k] = d;                     // ghost code 
      k++;                            // ghost code
      f += t3(a-d, (b+d)*2, (c+d)/2);
      k--;                            // ghost code
    }
  else 
    store_solution(); // ghost code
  return f;
}

/*@ requires n == N() && s == 0 && k == 0
  @ ensures \result == s
  @*/
int queens(int n) {
  return t3(~(~0<<n),0,0);
}
