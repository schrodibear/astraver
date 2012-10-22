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

public class negate {

    /*@ requires t != null;
      @ assigns t[0..t.length-1];
      @ ensures \forall integer k; 0 <= k < t.length ==> t[k] == -\old(t[k]);
      @*/
    static void negate(int t[]) {
	int i = 0;
	/*@ loop_invariant
	  @   0 <= i <= t.length &&
	  @   (\forall integer k; 0 <= k < i ==> t[k] == -\at(t[k],Pre)) &&
	  @   (\forall integer k; i <= k < t.length ==> t[k] == \at(t[k],Pre)) ;
	  @ // TODO: replace previous invariant by loop_assigns t[0..i-1];
	  @ loop_variant t.length-i;
	  @*/
	while (i < t.length) {
	    t[i] = -t[i];
	    i++;
	}

    }

}



/*
Local Variables:
compile-command: "make Negate.why3ide"
End:
*/

