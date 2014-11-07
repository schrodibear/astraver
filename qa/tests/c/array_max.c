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

/*
COST Verification Competition. vladimir@cost-ic0701.org

Challenge 1: Maximum in an array

Given: A non-empty integer array a.

Verify that the index returned by the method max() given below points to
an element maximal in the array.

*/

/*@ requires len > 0 && \valid_range(a,0,len-1);
  @ ensures 0 <= \result < len &&
  @   \forall integer i; 0 <= i < len ==> a[i] <= a[\result];
  @*/
int max(int *a, int len) {
  int x = 0;
  int y = len-1;
  /*@ loop invariant 0 <= x <= y < len &&
    @      \forall integer i;
    @         0 <= i < x || y < i < len ==>
    @         a[i] <= \max(a[x],a[y]);
    @ loop variant y - x;
    @*/
  while (x != y) {
    if (a[x] <= a[y]) x++;
    else y--;
  }
  return x;
}

/*
Local Variables:
compile-command: "make array_max.why3ide"
End:
*/

