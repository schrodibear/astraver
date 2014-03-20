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

//@+ CheckArithOverflow = no

/*@ lemma distr_right: 
  @   \forall integer x y z; x*(y+z) == (x*y)+(x*z);
  @*/

/*@ lemma distr_left: 
  @   \forall integer x y z; (x+y)*z == (x*z)+(y*z);
  @*/

/*@ lemma distr_right2: 
  @   \forall integer x y z; x*(y-z) == (x*y)-(x*z);
  @*/

/*@ lemma distr_left2: 
  @   \forall integer x y z; (x-y)*z == (x*z)-(y*z);
  @*/

public class Cube {
    /*@ requires x > 0;
      @ ensures \result == x * x * x;
      @*/
  public static int cube(int x) {
    int a = 1;
    int b = 0;
    int c = x;
    int z = 0;
    /*@ loop_invariant 
      @    0 <= c &&
      @    a == 3*(x-c) + 1 &&
      @    b == 3*(x-c)*(x-c) &&
      @    z == (x-c)*(x-c)*(x-c);
      @ loop_variant c;
      @*/
    while (c > 0) {
      z += a + b;
      b += 2*a + 1;
      a += 3;
      c--;
    }
    return z;
  }
}
