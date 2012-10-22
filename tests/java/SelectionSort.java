/**************************************************************************/
/*                                                                        */
/*  The Why platform for program certification                            */
/*                                                                        */
/*  Copyright (C) 2002-2011                                               */
/*                                                                        */
/*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud 11                */
/*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           */
/*    Yannick MOY, Univ. Paris-sud 11                                     */
/*    Romain BARDOU, Univ. Paris-sud 11                                   */
/*                                                                        */
/*  Secondary contributors:                                               */
/*                                                                        */
/*    Thierry HUBERT, Univ. Paris-sud 11  (former Caduceus front-end)     */
/*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          */
/*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        */
/*    Sylvie BOLDO, INRIA                 (floating-point support)        */
/*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  */
/*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       */
/*                                                                        */
/*  This software is free software; you can redistribute it and/or        */
/*  modify it under the terms of the GNU Lesser General Public            */
/*  License version 2.1, with the special exception on linking            */
/*  described in file LICENSE.                                            */
/*                                                                        */
/*  This software is distributed in the hope that it will be useful,      */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  */
/*                                                                        */
/**************************************************************************/

/*@ predicate Sorted{L}(int a[], integer l, integer h) =
  @   \forall integer i j; l <= i <= j < h ==> a[i] <= a[j] ;
  @*/

/*@ predicate Swap{L1,L2}(int a[], integer i, integer j) =
  @   \at(a[i],L1) == \at(a[j],L2) &&
  @   \at(a[j],L1) == \at(a[i],L2) &&
  @   \forall integer k; k != i && k != j ==> \at(a[k],L1) == \at(a[k],L2);
  @*/

/*@ inductive Permut{L1,L2}(int a[], integer l, integer h) {
  @  case Permut_refl{L}: 
  @   \forall int a[], integer l h; Permut{L,L}(a, l, h) ;
  @  case Permut_sym{L1,L2}: 
  @    \forall int a[], integer l h; 
  @      Permut{L1,L2}(a, l, h) ==> Permut{L2,L1}(a, l, h) ;
  @  case Permut_trans{L1,L2,L3}: 
  @    \forall int a[], integer l h; 
  @      Permut{L1,L2}(a, l, h) && Permut{L2,L3}(a, l, h) ==> 
  @        Permut{L1,L3}(a, l, h) ;
  @  case Permut_swap{L1,L2}: 
  @    \forall int a[], integer l h i j; 
  @       l <= i <= h && l <= j <= h && Swap{L1,L2}(a, i, j) ==> 
  @     Permut{L1,L2}(a, l, h) ;
  @ }
  @*/

class SelectionSort {

    /*@ requires t != null && 
      @    0 <= i < t.length && 0 <= j < t.length;
      @ assigns t[i],t[j];
      @ ensures Swap{Old,Here}(t,i,j);
      @*/
    void swap(int t[], int i, int j) {
	int tmp = t[i];
	t[i] = t[j];
	t[j] = tmp;
    }
    
    /*@ requires t != null;
      @ behavior sorted:
      @   ensures Sorted(t,0,t.length);
      @ behavior permutation:
      @   ensures Permut{Old,Here}(t,0,t.length-1);
      @*/
    void sort(int t[]) {
	int i,j;
	int mi,mv;
	/*@ loop_invariant 0 <= i;
	  @ for sorted: 
	  @  loop_invariant Sorted(t,0,i) && 
	  @   (\forall integer k1 k2 ; 
	  @      0 <= k1 < i <= k2 < t.length ==> t[k1] <= t[k2]) ;
	  @ for permutation:
	  @   loop_invariant Permut{Pre,Here}(t,0,t.length-1);
	  @ loop_variant t.length - i;
	  @*/
	for (i=0; i<t.length-1; i++) {
	    // look for minimum value among t[i..n-1]
	    mv = t[i]; mi = i;
	    /*@ loop_invariant i < j && i <= mi < t.length;
	      @ for sorted:
	      @  loop_invariant mv == t[mi] &&
	      @   (\forall integer k; i <= k < j ==> t[k] >= mv);
	      @ // useless ! for permutation:
	      @ // loop_invariant Permut{Pre,Here}(t,0,t.length-1);
	      @ loop_variant t.length - j;
	      @*/
	    for (j=i+1; j < t.length; j++) {
		if (t[j] < mv) { 
		    mi = j ; mv = t[j]; 
		}
	    }
	    Before: 
	    swap(t,i,mi);
	    //@ for permutation: assert Permut{Before,Here}(t,0,t.length-1);
	}
    }

}



/*
Local Variables:
compile-command: "make SelectionSort.why3ide"
End:
*/


