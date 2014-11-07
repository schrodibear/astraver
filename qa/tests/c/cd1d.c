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

#define D 10.0
#define T 1.0

/*@ predicate conflict(real s, real v) =
      \exists real t; 0<=t<=T && s - t * v < D;
*/

/*@ predicate cd1d(real s, real v) = D + T * v > s ; */

/*@ lemma completeness: \forall real s, v; v >= 0.0 ==>
             conflict(s,v) ==> cd1d(s,v); */

#define eps 0x1p-49

#define Dp (D+eps)

/*@ requires 100.>=s>=0. && 1. >=v >= 0.;
       behavior completeness:
          assumes cd1d(s,v);
          ensures \result == 1;
 */
int cd1d_double(double s, double v) {
  return (Dp+T*v>s) ? 1 : 0;
}
