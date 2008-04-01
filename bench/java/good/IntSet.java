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
/*  modify it under the terms of the GNU General Public                   */
/*  License version 2, as published by the Free Software Foundation.      */
/*                                                                        */
/*  This software is distributed in the hope that it will be useful,      */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  */
/*                                                                        */
/*  See the GNU General Public License version 2 for more details         */
/*  (enclosed in the file GPL).                                           */
/*                                                                        */
/**************************************************************************/

/*@ lemma mean_property : 
  @   \forall integer x y; x <= y ==> x <= (x+y)/2 <= y ;
  @*/

/*@ predicate is_sorted{L}(int[] t) {
  @   t != null && 
  @   \forall integer i j; 
  @     0 <= i && i <= j && j < t.length ==> t[i] <= t[j]
  @ }
  @*/

public class IntSet {

    public int t[];
    // pb with recursive def of type and logic in Jessie
    // @ invariant t_is_sorted: is_sorted(t);
    
    /*@	requires t.length <= 2147483647 && is_sorted(t);
      @ behavior search_success:
      @   ensures
      @   \result >= 0 ==> t[\result] == v;
      @ behavior search_failure:
      @   ensures \result < 0 ==> (\forall integer k; 
      @     0 <= k && k < t.length ==> t[k] != v);
      @*/
    public int binary_search(int v) {
	int l = 0, u = t.length-1;
	/*@ loop_invariant 
	  @   0 <= l && u <= t.length-1 && 
	  @   \forall integer k; 
	  @     0 <= k && k < t.length && t[k] == v ==> l <= k && k <= u;
	  @ decreases u-l ;
	  @*/
	while (l <= u ) {
	    int m = (l + u) / 2;
	    if (t[m] < v) l = m + 1; 
	    else if (t[m] > v) u = m - 1;
	    else return m;
	}
	return -1;
    }

}


/*
Local Variables: 
compile-command: "make IntSet"
End: 
*/


