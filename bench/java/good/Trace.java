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

class Trace {

    /* Example 0
     * We want the message: 
     *  "assertion `x < 9' cannot be established"
     * localized on `x < 9' 
     */

    /*@ ensures this.f == 0;
      @*/
    Trace() {
	f = 0;
    }

    /* Example 1 
     * We want the message: 
     *  "assertion `x < 9' cannot be established"
     * localized on `x < 9' 
     */
    
    /*@ requires x > 0;
      @*/
    int m1(int x) {
	//@ assert x >= 0 && x < 9; 
	return x+1;
    }

    /* Example 2 
     * We want the message: 
     *  "post-condition `\result > 10' of function m2 cannot be established"
     * localized on `return x+1'
     * Bonus: all lines involved in the execution path should be ~underlined 
     */
    /*@ requires x > 0 && x < 100;
      @ ensures \result != 0 && \result > 10;  
      @*/
    int m2(int x) {
	int y;
	if (x<50) 
	    return x+1;
	else 
	    y = x-1;
	return y;
    }


    /* Example 3 
     * We want the message: 
     *  "pre-condition `x > 0' for call to function m3 cannot be established"
     * localized on `m2(x)' 
     */
    /*@ requires x >= 0 && x < 50;
      @*/
    int m3(int x) {
	return m2(x);
    }


    /* Example 4 
     * Explanation expected: 
     *   "validity of loop invariant `0 <= y' at loop entrance"
     * localized on `while ...' 
     */
    void m4(int x) { 
	int y = x;
	/*@ loop_invariant 0 <= y && y <= x;
	  @ loop_variant y;
	  @*/
	while (y > 0)
	    {
	    y = y - 1;
	}
    }

    
    /* Example 5 
     * Explanation expected:
     *   "preservation of loop invariant `y = x'"
     * localized on the '}' closing the loop body 
     */
    
    void m5(int x) {
	int y = x;
	/*@ loop_invariant y == x;
	  @ loop_variant y;
	  @*/
	while (y > 0) {
	    y = y - 1;
	}
    }

    /* Example 6
     * Explanation expected:
     *   "arithmetic overflow"
     * localized on first "x", on "(byte)(x+1)" and on "(byte)(x+2)"
     */
    byte m6(byte x) {
	x += x+1;
	x = (byte)(x+1); 
	return (byte)(x+2);
    }

    /* Example 7
     * Explanation expected:
     *   "pointer dereferencing"
     * localized on "p.f"
     */
    int f; 
    int m7(Trace p)
    {
	return p.f;
    }

    /* Example 8
     * Explanation expected:
     *   "pointer dereferencing"
     * localized on "p.f"
     */
    /*@ assigns p.f;
      @ ensures p.f == 0;
      @*/
    void m8(Trace p)
    {
	p.f = 0;
    }

    
}



/*
Local Variables: 
mode: java
compile-command: "make Trace"
End: 
*/
