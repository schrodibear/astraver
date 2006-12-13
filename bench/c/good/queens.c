/****
t(a,b,c){int d=0,e=a&~b&~c,f=1;if(a)for(f=0;d=(e-=d)&-e;f+=t(a-d,(b+d)*2,(
c+d)/2));return f;}main(q){scanf("%d",&q);printf("%d\n",t(~(~0<<q),0,0));}
****/

/****** abstract sets of integers *******************************************/

//@ type iset

//@ predicate in_(int x, iset s)

//@ predicate included(iset a, iset b) { \forall int i; in_(i,a) => in_(i,b) }

//@ logic int card(iset s)
//@ axiom card_nonneg : \forall iset s; card(s) >= 0

//@ logic iset empty()
//@ axiom empty_def : \forall int i; !in_(i,empty())
//@ axiom empty_card : \forall iset s; card(s)==0 <=> s==empty()

//@ logic iset diff(iset a, iset b)
/*@ axiom diff_def : 
  @   \forall iset a, iset b; \forall int i;
  @     in_(i,diff(a,b)) <=> (in_(i,a) && !in_(i,b))
  @*/

//@ logic iset add(int x, iset a)
/*@ axiom add_def : 
  @   \forall iset s; \forall int x; \forall int i;
  @     in_(i,add(x,s))  <=> (i==x || in_(i,s))
  @*/

//@ logic iset remove(int x, iset s)
/*@ axiom remove_def : 
  @   \forall iset s; \forall int x; \forall int i;
  @     in_(i,remove(x,s))  <=> (in_(i,s) && i!=x)
  @*/

/*@ axiom remove_card : 
  @   \forall iset s; \forall int i;
  @     in_(i,s) => card(remove(i,s)) == card(s) - 1
  @*/

//@ logic int min_elt(iset s)
/*@ axiom min_elt_def : 
  @   \forall iset s; card(s) > 0 => 
  @     (in_(min_elt(s), s) &&
  @     \forall int i; in_(i,s) => min_elt(s) <= i)
  @*/

//@ logic iset singleton(int x)
/*@ axiom singleton_def : \forall int i, int j; in_(j,singleton(i)) <=> j==i
  @*/

//@ logic iset succ(iset s)
/*@ axiom succ_def_1 :  
  @   \forall iset s; \forall int i; in_(i,s) => in_(i+1,succ(s))
  @*/
/*@ axiom succ_def_2 :  
  @   \forall iset s; \forall int i; in_(i,succ(s)) => i>=1 && in_(i-1,s)
  @*/

//@ logic iset pred(iset s)
/*@ axiom pred_def_1 : 
  @   \forall iset s; \forall int i; i>=1 => in_(i,s) => in_(i-1,pred(s))
  @*/
/*@ axiom pred_def_2 : 
  @   \forall iset s; \forall int i; in_(i,pred(s)) => in_(i+1,s)
  @*/

//@ logic iset below(int n)
//@ axiom below_def : \forall int n, int i; in_(i, below(n)) <=> 0<=i<n
//@ axiom below_card : \forall int n; card(below(n)) == n

/****** interpretation of C ints as abstract sets of integers ***************/

//@ logic iset iset(int x)

//@ axiom iset_c_zero : \forall int x; iset(x)==empty() <=> x==0

/*@ axiom iset_c_remove : 
  @  \forall int x, int a, int b; 
  @    iset(b)==singleton(x) => in_(x,iset(a)) => iset(a-b)==remove(x, iset(a))
  @*/

// lowest bit trick
/*@ axiom iset_c_min_elt :
  @   \forall int x; x != 0 => iset(x&-x) == singleton(min_elt(iset(x)))
  @*/
/*@ axiom iset_c_min_elt_help :
  @   \forall int x; x != 0 <=> x&-x != 0
  @*/

/*@ axiom iset_c_diff :
  @  \forall int a, int b; iset(a&~b) == diff(iset(a), iset(b))
  @*/

/*@ axiom iset_c_add :
  @  \forall int x, int a, int b; 
  @    iset(b)==singleton(x) => !in_(x,iset(a)) => iset(a+b) == add(x, iset(a))
  @*/

//@ axiom iset_c_below : \forall int n; iset(~(~0<<n)) == below(n)

/****** helper lemmas *******************************************************/

/* @ axiom included_trans : \forall iset a, iset b, iset c;
  @   included(a,b) => included(b,c) => included(a,c)
  @*/

/* @ axiom included_diff : \forall iset a, iset b; included(diff(a,b), a) */

/* @ axiom included_remove : \forall iset a, int x; included(remove(x,a), a) */

/***************************************************************************/

// t1: termination of the for loop
int t1(int a, int b, int c){
  int d=0, e=a&~b&~c, f=1;
  if (a)
    /*@ variant card(iset(e-d)) */
    for (f=0; d=(e-=d)&-e; ) {
      f+=t1(a-d,(b+d)*2,(c+d)/2);
    }
  return f;
}

/****************************************************************************/

// t2: termination of the for loop: card(iset(a)) decreases
int t2(int a, int b, int c){
  int d=0, e=a&~b&~c, f=1;
  //@ label L
  if (a)
    /*@ invariant 
      @   included(iset(e-d), iset(e)) &&
      @   included(iset(e),\at(iset(e),L)) 
      @*/
    for (f=0; d=(e-=d)&-e; ) {
      //@ assert \exists int x; iset(d) == singleton(x) && in_(x,iset(e)) 
      //@ assert card(iset(a-d)) < card(iset(a))
      f+=t2(a-d,(b+d)*2,(c+d)/2);
    }
  return f;
}

/****************************************************************************/

//@ logic int N() // N queens on a NxN chessboard 
//@ axiom N_positive : N() > 0

// t and u have the same prefix [0..i[
/*@ predicate eq_prefix(int *t, int *u, int i) {
  @   \forall int k; 0 <= k < i => t[k]==u[k]
  @ } 
  @*/

//@ predicate eq_sol(int *t, int *u) { eq_prefix(t, u, N()) } 

int** sol; // sol[i] is the i-th solution
/*@ axiom dont_bother_me_I_am_a_ghost_1 : 
  @   \forall int i; \valid(sol+i) */
/*@ axiom dont_bother_me_I_am_a_ghost_2 : 
  @   \forall int i, int j; \valid(sol[i]+j) */

int s = 0; // next empty slot in sol for a solution

int* col; // current solution being built
int k;    // current row in the current solution

// s stores a partial solution, for the rows 0..k-1
/*@ predicate partial_solution(int k, int* s) {
  @   \forall int i; 0 <= i < k => 
  @     (\exists int j; 0 <= j < N() && iset(s[i]) == singleton(j)) &&
  @     (\forall int j; 0 <= j < i => s[i] != s[j] &&
  @                                   s[i]-s[j] != i-j &&
  @                                   s[i]-s[j] != j-i)
  @ }
  @*/

//@ predicate solution(int* s) { partial_solution(N(), s) }

// lemma
/*@ axiom partial_solution_eq_prefix:
  @   \forall int *t, int *u; \forall int k;
  @     partial_solution(k,t) => eq_prefix(t,u,k) => partial_solution(k,u)
  @*/

/*@ requires solution(col)
  @ assigns  s, sol[s][0..N()-1]
  @ ensures  s==\old(s)+1 && eq_sol(sol[\old(s)], col)
  @*/
void store_solution();

/*@ requires
  @   0 <= k && k + card(iset(a)) == N() && 0 <= s &&
  @   pre_a:: (\forall int i; in_(i,iset(a)) <=> 
  @            (0<=i<N() && \forall int j; 0<=j<k => !in_(i,iset(col[j])))) &&
  @   pre_b:: (\forall int i; i>=0 => (in_(i,iset(b)) <=> 
  @            (\exists int j; 0<=j<k && iset(col[j]) == singleton(i+j-k)))) &&
  @   pre_c:: (\forall int i; i>=0 => (in_(i,iset(c)) <=> 
  @            (\exists int j; 0<=j<k && iset(col[j]) == singleton(i+k-j)))) &&
  @   partial_solution(k, col)
  @ assigns
  @   col[k..], s, k, sol[s..][..]
  @ ensures  
  @   \result == s - \old(s) && \result >= 0 && k == \old(k) &&
  @   \forall int* t; ((solution(t) && eq_prefix(col,t,k)) <=>
  @                    (\exists int i; \old(s)<=i<s && eq_sol(t, sol[i])))
  @*/
int t3(int a, int b, int c){
  int d=0, e=a&~b&~c, f=1;
  //@ label L
  if (a)
    /*@ invariant 
      @   included(iset(e-d),iset(e)) && included(iset(e),\at(iset(e),L)) &&
      @   f == s - \at(s,L) && f >= 0 && k == \old(k) && 
      @   partial_solution(k, col) &&
      @   \forall int *t; 
      @     (solution(t) && 
      @      \exists int di; in_(di,diff(iset(e), \at(iset(e),L))) &&
      @          eq_prefix(col,t,k) && t[k]==di) <=>
      @     (\exists int i; \at(s,L)<=i<s && eq_sol(t, sol[i]))
      @ loop_assigns
      @   col[k..], s, k, sol[s..][..]
      @*/
    for (f=0; d=(e-=d)&-e; ) {
      //@ assert \exists int x; iset(d) == singleton(x) && in_(x,iset(a)) 
      col[k] = d;                     // ghost code 
      k++;                            // ghost code
      f += t3(a-d, (b+d)*2, (c+d)/2);
      k--;                            // ghost code
    }
  else 
    store_solution(); // ghost code
  return f;
}

/*@ requires 
  @   n == N() && s == 0 && k == 0
  @ ensures 
  @   \result == s &&
  @   \forall int* t; 
  @      solution(t) <=> (\exists int i; 0<=i<\result && eq_sol(t,sol[i]))
  @*/
int queens(int n) {
  return t3(~(~0<<n),0,0);
}


/****************************************************************************/

/* @ axiom bwand_set : \forall int x, int y; 
  @   \forall int i; b_in(i,x&y) <=> (b_in(i,x) && b_in(i,y)) 
  @*/

/* @ predicate included(int x, int y) { 
  @   \forall int i; b_in(i,x) => b_in(i,y) 
  @ } 
  @*/

/* @ axiom included_trans : \forall int x, int y, int z;
  @   included(x,y) => included(y,z) => included(x,z)
  @*/

/* @ axiom included_bwand_l : \forall int x, int y; included(x&y, x) */

/* @ axiom included_bwand_r : \forall int x, int y; included(x&y, y) */

/* @ axiom included_sub : \forall int x, int y;
  @   included(x,y) => included(y-x, y)
  @*/

/* @ axiom included_nbits : \forall int x, int y;
  @   included(x,y) => nbits(y-x) == nbits(y) - nbits(x)
  @*/

/* @ axiom included_lowest_bit : \forall int x; included(lowest_bit(x), x) */

/* @ logic int singleton(int i) */ // this is 2^i

/* @ axiom singleton_def : \forall int i, int j; b_in(j,singleton(i)) <=> j==i
  @*/

/* @ axiom lowest_bit_is_singleton : \forall int x;
  @   x != 0 => \exists int i; lowest_bit(x) == singleton(i)
  @*/

/* @ logic int all_ones(int n) */ // this is 2^n-1, that 11...1 with n ones

/* @ axiom all_ones_def : \forall int n; 
  @   \forall int i; b_in(i, all_ones(n)) <=> 0 <= i < n
  @*/   

/* @ axiom help_1: \forall int a, int n, int i;
  @   b_in(i,a) => included(a,all_ones(n)) => 0 <= i < n
  @*/

// @ axiom all_ones_trick : \forall int n; ~(~0<<n) == all_ones(n)

// @ axiom nbits_all_ones : \forall int n; nbits(all_ones(n))==n

/* @ axiom b_in_lsl : \forall int i, int x;
  @   b_in(i,x) <=> b_in(i+1, x*2)
  @*/

/* @ axiom b_in_lsr : \forall int i, int x; i>0 =>
  @   (b_in(i,x) <=> b_in(i-1, x/2))
  @*/

