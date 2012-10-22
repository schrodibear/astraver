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

public class Switch {

    /*@ behavior normal:
      @   assigns \nothing;
      @   ensures (n==0 || n==1) <==> \result == 0;
      @*/
    public static int test1 (int n) {
	int r;
	switch(n) {
	case 0:
	case 1:
	    r = 0;
	    break;
	default:
	    r = 2;
	}
	return r;
    }

    /*@ behavior normal:
      @   assigns \nothing;
      @   ensures ((n==4 || n==7) <==> \result == 1) &&
      @            ((n==0 || n==1) <==> \result == 0);
      @*/
    public static int test2 (int n) {
	int r;
	switch(n) {
	case 0:
	case 1:
	    r = 0;
	    break;
	case 4:
	case 7:
	    r = 1;
	    break;
	case 12:
	default:
	case 26:
	    r = 2;
	}
	return r;
    }

}

/*
Local Variables:
compile-command: "make Switch.why3ide"
End:
*/

