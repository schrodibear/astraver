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

//@+ CheckArithOverflow = no

/* Dijkstra's dutch flag */

//@ predicate is_color(integer c) = Flag.BLUE <= c && c <= Flag.RED ;

/*@ predicate is_color_array{L}(int t[]) =
  @   t != null && 
  @   \forall integer i; 0 <= i < t.length ==> is_color(t[i]) ;
  @*/

/*@ predicate is_monochrome{L}(int t[],integer i, integer j, int c) =
  @   \forall integer k; i <= k < j ==> t[k] == c ;
  @*/



class Flag {
    
    public static final int BLUE = 1, WHITE = 2, RED = 3;
    
    int t[];
    //@ invariant t_non_null: t != null;
    //@ invariant is_color_array_inv: is_color_array(t);

    /*@ requires 0 <= i <= j <= t.length ;
      @ ensures \result <==> is_monochrome(t,i,j,c);
      @*/
    public boolean isMonochrome(int i, int j, int c) {
    	/*@ loop_invariant i <= k && 
	  @   (\forall integer l; i <= l < k ==> t[l]==c);
    	  @ loop_variant j - k;
	  @*/
	for (int k = i; k < j; k++) if (t[k] != c) return false;
	return true;
    }

    /*@ requires 0 <= i < t.length && 0 <= j < t.length;
      @ behavior i_j_swapped:
      @   assigns t[i],t[j];
      @   ensures t[i] == \old(t[j]) && t[j] == \old(t[i]);
      @*/
    private void swap(int i, int j) {
	int z = t[i];
	t[i] = t[j];
	t[j] = z;
    }

    /*@ behavior sorts:
      @   assigns t[..];
      @   ensures 
      @     (\exists integer b r; 
      @          is_monochrome(t,0,b,BLUE) &&
      @          is_monochrome(t,b,r,WHITE) &&
      @          is_monochrome(t,r,t.length,RED));
      @*/
    public void flag() {
	int b = 0;
	int i = 0;
	int r = t.length;
	/*@ loop_invariant
	  @   is_color_array(t) &&
	  @   0 <= b <= i <= r <= t.length &&
	  @   is_monochrome(t,0,b,BLUE) &&
	  @   is_monochrome(t,b,i,WHITE) &&
          @   is_monochrome(t,r,t.length,RED);
	  @ loop_variant r - i; 
	  @*/
	while (i < r) {
	    switch (t[i]) {
	    case BLUE:  
		swap(b++, i++);
		break;	    
	    case WHITE: 
		i++; 
		break;
	    case RED: 
		swap(--r, i);
		break;
	    }
	}
    }
}



/*
Local Variables: 
compile-command: "make Flag"
End: 
*/
