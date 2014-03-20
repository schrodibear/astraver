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

class Fresh2 {

    int x;

    /*@ assigns \nothing;
      @ allocates this;
      @ ensures \fresh(this);
      @*/
    Fresh2 ();

    /*@ assigns \nothing;
      @ allocates \result;
      @ ensures \result != null && \fresh(\result);
      @*/
    static Fresh2 create() {
        return new Fresh2();
    }

    void test() {
        Fresh2 f;
        f = create ();
        //@ assert this != f;
    }

    static void smoke_detector() {
        Fresh2 _s1 = create ();
        Fresh2 _s2 = create ();
        //@ assert 0 == 1;
    }

}


/*
Local Variables:
compile-command: "LC_ALL=C make Fresh2.why3ide"
End:
*/
