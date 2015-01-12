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

/* right way to compute the mean of two integers without overflow
   (extracted from binary_search.c) */

//@ axiom mean_1 : \forall int x; 0 <= x => 0 <= x/2 <= x

//@ requires 0 <= l <= r 
int mean(int l, int r) {
  return l + (r - l)/2;
}

//@ requires l <= r 
unsigned int umean(unsigned int l, unsigned int r) {
  //@ assert 0 <= (r-l)/2 <= r-l
  return l + (r - l)/2;
}

//@ ensures (\result == x <= y) || (\result == y <= x)
int min_int(int x, int y);

//@ ensures (\result == x >= y) || (\result == y >= x)
int max_int(int x, int y);

//@ requires 0 <= x && 0 <= y
int mean2(int x, int y) {
  int min = min_int(x,y), max = max_int(x,y);
  return min + (max - min)/2;
}