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

public class SimpleNew {

    int simple_val;

    /*@ behavior normal:
      @   assigns \nothing; // not `this.simple_val'; 
      @   ensures this.simple_val == 0;
      @*/
    SimpleNew() {
	this(0);
    }

    /*@ behavior normal:
      @   assigns \nothing; 
      @   ensures this.simple_val == n;
      @*/
    SimpleNew(int n) {
	simple_val = n;
    }

    /*@ behavior normal:
      @   assigns \nothing;
      @   ensures this.simple_val == n + m;
      @*/
    SimpleNew(int n,int m) {
	this(n+m); 
    }

    /*@ behavior normal:
      @   ensures \result == 17;
      @*/
    public static int test1() {
	SimpleNew t = new SimpleNew(17);
	return t.simple_val;
    }

    /*@ behavior normal:
      @   ensures \result == 0;
      @*/
    public static int test2() {
	SimpleNew t = new SimpleNew();
	return t.simple_val;
    }

    /*@ behavior normal:
      @   assigns \nothing;
      @   ensures \result == 17;
      @*/
    public static int test3() {
	SimpleNew t = new SimpleNew(10,7);
	return t.simple_val;
    }
}


/*
Local Variables: 
compile-command: "make SimpleNew.io"
End: 
*/
