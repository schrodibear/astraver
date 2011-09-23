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

/*@ predicate divides(int x, int y) {
  @   \exists int q; y == q*x
  @ }
  @*/

/*@ axiom div_mod_property:
  @  \forall int x; \forall int y; 
  @    x >=0 && y > 0 => x == y*(x/y) + (x%y) 
  @*/

/*@ requires x >= 0 && y >= 0
  @ ensures 
  @  (divides_both::
  @    divides(\result,x) && divides(\result,y)) &&
  @  (is_greatest_divisor::
  @    \forall int z;
  @      z>0 && divides(z,x) && divides(z,y) => z>=\result) && 
  @  (bezout_property::
  @    \exists int a; \exists int b; a*x+b*y == \result)
  @*/
int gcd(int x, int y) {
  //@ ghost int a = 1
  //@ ghost int b = 0
  //@ ghost int c = 0
  //@ ghost int d = 1
  /*@ invariant 
    @    a*\old(x)+b*\old(y)==x && 
    @    c*\old(x)+d*\old(y)==y 
    @ variant y
    @*/
  while (y > 0) {
    int r = x % y;
    //@ ghost int q = x / y
    //@ ghost int ta = a
    //@ ghost int tb = b
    x = y;
    y = r;
    //@ set a = c 
    //@ set b = d
    //@ set c = ta - c * q
    //@ set d = tb - d * q
  }
  return x;
}

