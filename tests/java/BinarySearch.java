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

// RUNSIMPLIFY this tells regtests to run Simplify in this example

//+ CheckArithOverflow = yes

/* lemma mean_property1 :
  @   \forall integer x y; x <= y ==> x <= (x+y)/2 <= y;
  @*/

/* lemma mean_property2 :
  @   \forall integer x y; x <= y ==> x <= x+(y-x)/2 <= y;
  @*/

/* lemma div2_property :
  @   \forall integer x; 0 <= x ==> 0 <= x/2 <= x;
  @*/

/*@ predicate is_sorted{L}(int[] t) =
  @   t != null &&
  @   \forall integer i j;
  @     0 <= i && i <= j && j < t.length ==> t[i] <= t[j] ;
  @*/


class BinarySearch {

    /* binary_search(t,v) search for element v in array t
       between index 0 and t.length-1
       array t is assumed to be sorted in increasing order
       returns an index i between 0 and t.length-1 where t[i] equals v,
       or -1 if no element in t is equal to v
    */

    /*@ requires t != null;
      @ ensures -1 <= \result < t.length;
      @ behavior success:
      @   ensures \result >= 0 ==> t[\result] == v;
      @ behavior failure:
      @  assumes is_sorted(t);
      @  // assumes
      @  //   \forall integer k1 k2;
      @  //      0 <= k1 <= k2 <= t.length-1 ==> t[k1] <= t[k2];
      @  ensures \result == -1 ==>
      @    \forall integer k; 0 <= k < t.length ==> t[k] != v;
      @*/
    static int binary_search(int t[], int v) {
	int l = 0, u = t.length - 1;
	/*@ loop_invariant
	  @   0 <= l && u <= t.length - 1;
	  @ for failure:
	  @  loop_invariant
	  @    \forall integer k; 0 <= k < t.length ==> t[k] == v ==> l <= k <= u;
	  @ loop_variant
	  @   u-l ;
	  @*/
	while (l <= u ) {
	    int m;
            m = (u + l) / 2;
            // fix: m = l + (u - l) / 2;
            // the following assertion helps provers
            //@ assert l <= m <= u;
	    if (t[m] < v) l = m + 1;
	    else if (t[m] > v) u = m - 1;
	    else return m;
	}
	return -1;
    }

}

/*
Local Variables:
compile-command: "make BinarySearch.why3ide"
End:
*/


