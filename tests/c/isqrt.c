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


#pragma JessieIntegerModel(math)

//@ logic integer sqr(integer x) = x * x;

/*@ requires x >= 0;
  @ ensures \result >= 0 && sqr(\result) <= x && x < sqr(\result + 1);
  @*/
int isqrt(int x) {
  int count = 0, sum = 1;
  /*@ loop invariant count >= 0 && x >= sqr(count) && sum == sqr(count+1);
    @ loop variant  x - count; 
    @*/
  while (sum <= x) sum += 2 * ++count + 1;
  return count;
}

//@ ensures \result == 4;
int main () {
  int r;
  r = isqrt(17);
  //@ assert r < 4 ==> \false;
  //@ assert r > 4 ==> \false;
  return r;
}

/*
Local Variables:
compile-command: "make isqrt.why3ide"
End:
*/


