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

/*@ axiomatic integer_max {
  @   logic integer max(integer x, integer y);
  @   axiom max_is_ge : \forall integer x y; max(x,y) >= x && max(x,y) >= y;
  @   axiom max_is_some : \forall integer x y; max(x,y) == x || max(x,y) == y;
  @ }
  @*/

public class ArrayMax {


    /*@ requires a.length > 0;
      @ ensures 0 <= \result < a.length &&
      @   \forall integer i; 0 <= i < a.length ==> a[i] <= a[\result];
      @*/
    public static int max(int[] a) {
        int x = 0;
        int y = a.length-1;
        /*@ loop_invariant 0 <= x <= y < a.length &&
          @      \forall integer i;
          @         0 <= i < x || y < i < a.length ==>
          @         a[i] <= max(a[x],a[y]);
          @ loop_variant y - x;
          @*/
        while (x != y) {
            if (a[x] <= a[y]) x++;
                else y--;
        }
        return x;
    }

}

/*
Local Variables:
compile-command: "make ArrayMax.why3ide"
End:
*/

