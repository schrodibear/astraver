/**************************************************************************/
/*                                                                        */
/*  The Why platform for program certification                            */
/*                                                                        */
/*  Copyright (C) 2002-2014                                               */
/*                                                                        */
/*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud                   */
/*    Claude MARCHE, INRIA & Univ. Paris-sud                              */
/*    Yannick MOY, Univ. Paris-sud                                        */
/*    Romain BARDOU, Univ. Paris-sud                                      */
/*                                                                        */
/*  Secondary contributors:                                               */
/*                                                                        */
/*    Thierry HUBERT, Univ. Paris-sud  (former Caduceus front-end)        */
/*    Nicolas ROUSSET, Univ. Paris-sud (on Jessie & Krakatoa)             */
/*    Ali AYAD, CNRS & CEA Saclay      (floating-point support)           */
/*    Sylvie BOLDO, INRIA              (floating-point support)           */
/*    Jean-Francois COUCHOT, INRIA     (sort encodings, hyps pruning)     */
/*    Mehdi DOGGUY, Univ. Paris-sud    (Why GUI)                          */
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

/*@ lemma mean_property : 
  @   \forall integer x y; x <= y ==> x <= (x+y)/2 <= y; */


/*@ predicate sorted{L}(long t[]) {
  @   \forall integer i j; 0 <= i && i <= j && j < t.length ==>
  @          t[i] <= t[j] } */

public class Search {

    long t[];
    // pb with recursive def of type and logic in Jessie
    // @ invariant t_sorted: t != null && sorted(t);

    /*@ requires t != null && t.length < 2147483647 && sorted(t);
      @ behavior search_success:
      @   ensures \result >= 0 ==> t[\result] == v;
      @ behavior search_failure:
      @   ensures \result < 0 ==> 
      @     \forall integer k; 0 <= k && k < t.length ==> t[k] != v;
      @*/
    int binary_search(long v) {
	int l = 0, u = t.length-1;
	/*@ loop_invariant 
	  @   0 <= l && u <= t.length-1 &&
	  @     \forall integer i; 
	  @        0 <= i && i < t.length ==> t[i] == v ==> l <= i && i <= u;
	  @ loop_variant u-l ;
	  @*/
	while (l <= u ) {
	    int m = (l + u) / 2;
	    //@ assert l <= m && m <= u;
	    if (t[m] < v) l = m + 1;
	    else if (t[m] > v) u = m - 1;
	    else return m;
	}
	return -1;
    }
}


/*
Local Variables: 
compile-command: "make Search"
End: 
*/

