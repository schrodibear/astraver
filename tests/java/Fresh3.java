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

//@+ SeparationPolicy = None

class Int { int f; }

class Fresh3 {

  Int i;

/*@ assigns this.i;
  @ allocates this.i;
  @ ensures this.i != null && \fresh(this.i);
  @*/
void create() {
    this.i = new Int();
}

/*@ requires f != null && this.i != null && this != f;
  @*/
void test(Fresh3 f) {
  f.create();
  //@ assert this.i != f.i;
}

static void smoke_detector() {
    Fresh3 s1, s2;
    s1 = new Fresh3();
    s2 = new Fresh3();
    s1.create();
    s2.create();
    //@ assert 0 == 1;
}

}

/*
Local Variables:
compile-command: "LC_ALL=C make Fresh3.why3"
End:
*/
