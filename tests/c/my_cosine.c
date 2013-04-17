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

// does not work: RUN GAPPA: will ask regtests to run Gappa on this program
// does not work anymore: RUN COQ: use why3 instead


/*@ lemma method_error: \forall real x;
  @     \abs(x) <= 0x1p-5 ==> \abs(1.0 - x*x*0.5 - \cos(x)) <= 0x1p-24;
  @*/

/*@ requires \abs(x) <= 0x1p-5;
  @ ensures \abs(\result - \cos(x)) <= 0x1p-23;
  @*/
float my_cos1(float x) {
  //@ assert \abs(1.0 - x*x*0.5 - \cos(x)) <= 0x1p-24;
  return 1.0f - x * x * 0.5f;
}


/*@ requires \abs(x) <= 0x1p-5 && \round_error(x) == 0.0;
  @ ensures \abs(\result - \cos(x)) <= 0x1p-23;
  @*/
float my_cos2(float x) {
  //@ assert \exact(x) == x;
  float r = 1.0f - x * x * 0.5f;
  //@ assert \abs(\exact(r) - \cos(x)) <= 0x1p-24;
  return r;
}


/*@ requires \abs(\exact(x)) <= 0x1p-5
  @     && \round_error(x) <= 0x1p-20;
  @ ensures \abs(\exact(\result) - \cos(\exact(x))) <= 0x1p-24
  @     && \round_error(\result) <= \round_error(x) + 0x3p-24;
  @*/
float my_cos3(float x) {
  float r = 1.0f - x * x * 0.5f;
  //@ assert \abs(\exact(r) - \cos(\exact(x))) <= 0x1p-24;  // by interval
  return r;
}

/*@ requires \abs(x) <= 0.07 ;
  @ ensures \abs(\result - \cos(x)) <= 0x1.3p-20;
  @*/
float my_cos4(float x) {
  //@ assert \abs(1.0 - x*x*0.5 - \cos(x)) <= 0x1.2p-20;
  return 1.0f - x * x * 0.5f;
}


/*
Local Variables:
compile-command: "make my_cosine.why3ide"
End:
*/


