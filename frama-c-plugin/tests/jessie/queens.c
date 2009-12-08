/**************************************************************************/
/*                                                                        */
/*  The Why platform for program certification                            */
/*  Copyright (C) 2002-2008                                               */
/*    Romain BARDOU                                                       */
/*    Jean-François COUCHOT                                               */
/*    Mehdi DOGGUY                                                        */
/*    Jean-Christophe FILLIÂTRE                                           */
/*    Thierry HUBERT                                                      */
/*    Claude MARCHÉ                                                       */
/*    Yannick MOY                                                         */
/*    Christine PAULIN                                                    */
/*    Yann RÉGIS-GIANAS                                                   */
/*    Nicolas ROUSSET                                                     */
/*    Xavier URBAIN                                                       */
/*                                                                        */
/*  This software is free software; you can redistribute it and/or        */
/*  modify it under the terms of the GNU Library General Public           */
/*  License version 2, with the special exception on linking              */
/*  described in file LICENSE.                                            */
/*                                                                        */
/*  This software is distributed in the hope that it will be useful,      */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  */
/*                                                                        */
/**************************************************************************/

/* Verification of the following 2 lines code for the N queens:

t(a,b,c){int d=0,e=a&~b&~c,f=1;if(a)for(f=0;d=(e-=d)&-e;f+=t(a-d,(b+d)*2,(
c+d)/2));return f;}main(q){scanf("%d",&q);printf("%d\n",t(~(~0<<q),0,0));}
*/

/****** abstract sets of integers *******************************************/

/*@ axiomatic integer_sets {

  type int_set;

  predicate in_(integer x, int_set s);

  predicate included(int_set a, int_set b) = \forall integer i; in_(i,a) ==> in_(i,b);

  logic integer card(int_set s);
  axiom card_nonneg : \forall int_set s; card(s) >= 0;

  logic int_set empty;

  axiom empty_def : \forall integer i; !in_(i,empty);
  axiom empty_card : \forall int_set s; card(s)==0 <==> s==empty;

  logic int_set diff(int_set a, int_set b);
  axiom diff_def : 
    \forall int_set a, b, integer i;
       in_(i,diff(a,b)) <==> (in_(i,a) && !in_(i,b));

  logic int_set add(integer x, int_set a);
  axiom add_def : 
     \forall int_set s, integer x, integer i;
       in_(i,add(x,s)) <==> (i==x || in_(i,s));

  logic int_set remove(integer x, int_set s);
  axiom remove_def : 
     \forall int_set s, integer x, integer i;
       in_(i,remove(x,s))  <==> (in_(i,s) && i!=x);

  axiom remove_card : 
     \forall int_set s, integer i;
       in_(i,s) ==> card(remove(i,s)) == card(s) - 1;

  logic integer min_elt(int_set s);
  axiom min_elt_def : 
     \forall int_set s; card(s) > 0 ==> 
       (in_(min_elt(s), s) &&
       \forall integer i; in_(i,s) ==> min_elt(s) <= i);

  logic int_set singleton(integer x);
  axiom singleton_def : 
    \forall integer i, integer j; in_(j,singleton(i)) <==> j==i;

  logic int_set succ(int_set s);
  axiom succ_def_1 :  
     \forall int_set s, integer i; in_(i,s) ==> in_(i+1,succ(s));

  axiom succ_def_2 :  
     \forall int_set s, integer i; in_(i,succ(s)) ==> i>=1 && in_(i-1,s);

  logic int_set pred(int_set s);
  axiom pred_def_1 : 
     \forall int_set s, integer i; i>=1 ==> in_(i,s) ==> in_(i-1,pred(s));

  axiom pred_def_2 : 
     \forall int_set s, integer i; in_(i,pred(s)) ==> in_(i+1,s);

  logic int_set below(integer n);
  axiom below_def : \forall integer n, integer i; in_(i, below(n)) <==> 0<=i<n;
  axiom below_card : \forall integer n; card(below(n)) == n;

  }
*/

/****** interpretation of C ints as abstract sets of integers ***************/

/*@ axiomatic C_ints_as_sets {

  logic int_set iset(int x);

  axiom iset_c_zero : 
  \forall int x; iset(x)==empty <==> x==0;

  axiom iset_c_remove : 
    \forall integer x, int a, int b; 
       iset(b)==singleton(x) ==> in_(x,iset(a)) ==> 
         iset((int)(a-b))==remove(x, iset(a));

  // lowest bit trick
  axiom iset_c_min_elt :
     \forall int x; x != 0 ==> iset((int)(x&-x)) == singleton(min_elt(iset(x)));

  axiom iset_c_diff :
    \forall int a, int b; iset((int)(a&~b)) == diff(iset(a), iset(b));

  axiom iset_c_add :
    \forall integer x, int a, int b; 
      iset(b)==singleton(x) ==> !in_(x,iset(a)) ==> 
        iset((int)(a+b)) == add(x, iset(a));

// @ axiom iset_c_succ : \forall int a; iset(a*2) == succ(iset(a))

// @ axiom iset_c_pred : \forall int a; iset(a/2) == pred(iset(a))

  axiom iset_c_below : \forall int n; iset((int)(~(~0<<n))) == below(n);

  }
*/

/*@

  lemma iset_c_min_elt_help :
     \forall int x; x != 0 <==> (int)(x&-x) != 0;

*/

/****** helper lemmas *******************************************************/

/* @ axiom included_trans : \forall iset a, iset b, iset c;
  @   included(a,b) ==> included(b,c) ==> included(a,c)
  @*/

/* @ axiom included_diff : \forall iset a, iset b; included(diff(a,b), a) */

/* @ axiom included_remove : \forall iset a, int x; included(remove(x,a), a) */

/***************************************************************************/

#pragma JessieIntegerModel(exact)
#pragma SeparationPolicy(none)

// t1: termination 

//@ decreases card(iset(a));
int t1(int a, int b, int c){
  int d, e=a&~b&~c, f=1;
  //@ ghost L:
  if (a)
    /*@ loop invariant included(iset(e),\at(iset(e),L));
        loop variant card(iset(e)); */
    for (f=0; d=e&-e; e-=d) {
      //@ assert \exists integer x; iset(d) == singleton(x) && in_(x,iset(e));
      f+=t1(a-d,(b+d)*2,(c+d)/2);
    }
  return f;
}

/****************************************************************************/

/*@ axiomatic N_queens {

  logic integer N; // N queens on a NxN chessboard 
  axiom N_positive : N > 0;

  }
*/

/*@

  // t and u have the same prefix [0..i[
  predicate eq_prefix{L}(int *t, int *u, integer i) =
     \forall integer k; 0 <= k < i ==> t[k]==u[k];

  predicate eq_sol{L}(int *t, int *u) = eq_prefix(t, u, N);

*/

//@ ghost int** sol; // sol[i] is the i-th solution

//@ ghost int s = 0; // next empty slot in sol for a solution

//@ ghost int* col; // current solution being built
//@ ghost int k;    // current row in the current solution

/*@ 
    
    lemma dont_bother_me_I_am_a_ghost_1{L} : 
     \forall int i; \valid(sol+i);

    lemma dont_bother_me_I_am_a_ghost_2{L} : 
     \forall int i, int j; \valid(sol[i]+j);

    lemma dont_bother_me_I_am_a_ghost_3{L} : 
     \forall int i; \valid(col+i);

*/

// s stores a partial solution, for the rows 0..k-1
/*@ predicate partial_solution{L}(integer k, int* s) =
  @   \forall integer i; 0 <= i < k ==> 
  @     0 <= s[i] < N &&
  @     (\forall int j; 0 <= j < i ==> s[i] != s[j] &&
  @                                   s[i]-s[j] != i-j &&
  @                                   s[i]-s[j] != j-i);
  @
  @*/

//@ predicate solution{L}(int* s) = partial_solution(N, s);

/*@ lemma partial_solution_eq_prefix{L}:
  @   \forall int *t, int *u; \forall integer k;
  @     partial_solution(k,t) ==> eq_prefix(t,u,k) ==> partial_solution(k,u);
  @*/

/*@ predicate lt_sol{L}(int *s1, int *s2) =
  @   \exists integer i; 0 <= i < N && eq_prefix(s1, s2, i) && s1[i] < s2[i];
  @*/

/* s[a..b[ is sorted for lt_sol */
/*@ predicate sorted{L}(int **s, integer a, integer b) =
  @   \forall integer i, integer j; a <= i < j < b ==> lt_sol(s[i], s[j]);
  @*/

/*@ requires x != 0;
    ensures  \result == min_elt(iset(x)); */
int min_elt(int x);

/*@ requires solution(col);
  @ assigns  s, sol[s][0..N-1];
  @ ensures  s==\old(s)+1 && eq_sol(sol[\old(s)], col);
  @*/
void store_solution();

/*@ requires
  @   0 <= k && k + card(iset(a)) == N && 0 <= s &&
  @   pre_a: (\forall int i; in_(i,iset(a)) <==> 
  @            (0<=i<N && \forall int j; 0<=j<k ==> i != col[j])) &&
  @   pre_b: (\forall int i; i>=0 ==> (in_(i,iset(b)) <==> 
  @            (\exists int j; 0<=j<k && col[j] == i+j-k))) &&
  @   pre_c: (\forall int i; i>=0 ==> (in_(i,iset(c)) <==> 
  @            (\exists int j; 0<=j<k && col[j] == i+k-j))) &&
  @   partial_solution(k, col);
  @ decreases 
  @   card(iset(a));
  @ assigns
  @   col[k..], s, k, sol[s..][..];
  @ ensures  
  @   \result == s - \old(s) && \result >= 0 && k == \old(k) &&
  @   sorted(sol, \old(s), s) &&
  @   \forall int* t; ((solution(t) && eq_prefix(col,t,k)) <==>
  @                    (\exists int i; \old(s)<=i<s && eq_sol(t, sol[i])));
  @*/
int t3(int a, int b, int c){
  int d, e=a&~b&~c, f=1;
  //@ ghost L:
  if (a)
    /*@ loop invariant 
      @   included(iset(e),\at(iset(e),L)) &&
      @   f == s - \at(s,L) && f >= 0 && k == \at(k,L) && 
      @   partial_solution(k, col) &&
      @   sorted(sol, \at(s,L), s) &&
      @   \forall int *t; 
      @     (solution(t) && 
      @      \exists int di; in_(di, diff(\at(iset(e),L), iset(e))) &&
      @          eq_prefix(col,t,k) && t[k]==di) <==>
      @     (\exists int i; \at(s,L)<=i<s && eq_sol(t, sol[i]));
      @ loop assigns
      @   col[k..], s, k, sol[s..][..];
      @ loop variant 
      @   card(iset(e)); 
      @*/
    for (f=0; d=e&-e; e-=d) {
      //@ assert \exists int x; iset(d) == singleton(x) && in_(x,iset(a)) ;
      //@ ghost col[k] = min_elt(d);            // ghost code 
      //@ ghost k++;                            // ghost code
      f += t3(a-d, (b+d)*2, (c+d)/2);
      //@ ghost k--;                            // ghost code
    }
  else                // ghost code
    store_solution(); // ghost code
  return f;
}

/*@ requires 
  @   n == N && s == 0 && k == 0;
  @ ensures 
  @   \result == s &&
  @   sorted(sol, 0, s) &&
  @   \forall int* t; 
  @      solution(t) <==> (\exists int i; 0<=i<\result && eq_sol(t,sol[i]));
  @*/
int queens(int n) {
  return t3(~(~0<<n),0,0);
}



/* 
Local Variables:
compile-command: "PPCHOME=../.. LC_ALL=C make queens"
End:
*/
