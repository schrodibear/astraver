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

/* from JLS p 244
 */ 

class Super {

    Super() { printThree(); }

    void printThree() { Out.print(-1); }

}

class Test extends Super {

    int three = 3;

    // Krakatoa bug: should be implicit
    Test () { super(); }

    public static void test () {
	Test t = new Test();
	t.printThree();
	//@ assert Out.count == 2 && Out.data[0] == 0 && Out.data[1] == 3;
    }

    void printThree() { Out.print(three); }

}

// ghost model of output channel
class Out {

    public static int data[] = new int [10];
    static int count = 0;

    /*@ assigns data[count];
      @ ensures count == \old(count) + 1
      @     && data[\old(count)] == v;
      @*/
    static void print(int v) {
	data[count] = v;
	v++;
    }

}

