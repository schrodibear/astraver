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

//////////////////////////////////////////////////////////////////////

class C1 {

    int[] t;
    //@ invariant C1_t_inv: t != null && t.length >= 1;

    void m(int[] p) {
	p[0] = 1;
   }

    void main() {
	m(t);
    }

}

//////////////////////////////////////////////////////////////////////

class C2 {

    static int[] t;
    //@ static invariant C2_t_inv: t != null && t.length >= 1;

    void m(int[] p) {
	p[0] = 1;
   }

    void main() {
	m(t);
    }

}

//////////////////////////////////////////////////////////////////////

class C3 {

    static Object t;
    //@ static invariant C3_t_inv: t != null;

    void m() {
	t = new Object();
	//@ assert t != null; 
   }

}

//////////////////////////////////////////////////////////////////////

class C4 {
    static int[] t; 
    //@ static invariant C4_t_inv: t != null && t.length == 10;
}

class C5 {
    void m() {
	int i = C4.t[0]; 
    }
}



/*
Local Variables: 
compile-command: "make Invariants"
End: 
*/


