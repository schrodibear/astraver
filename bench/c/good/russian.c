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

// this example was contributed by Daniel Zingaro

//@ axiom div2 : \forall int a; 0 < a => 0 <= a/2 < a
//@ axiom mul0 : \forall int a; 0 * a == 0

//@ axiom mul_odd : \forall int a, int b; a%2==1 => a*b == (a/2)*(b*2)+b
//@ axiom mul_even: \forall int a, int b; a%2!=1 => a*b == (a/2)*(b*2)

/*@ requires x >= 0 && y >= 0
  @ ensures
  @   \result == x * y
    @*/
int mult(int x, int y){
  int a = x, b = y, z = 0;
  /*@ invariant 0 <= a && 0 <= b && a * b + z == x * y
    @ variant a */
  while (a > 0) {
    if (a %2 == 1) z += b;
    a /= 2; b *= 2;
  }
  return z;
}
