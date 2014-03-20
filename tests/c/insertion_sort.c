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

// RUNSIMPLIFY: will ask regtests to run Simplify on this program

#pragma JessieIntegerModel(math)

#include "sorting.h"

/*@ requires \valid(t+(0..n-1));
  @ ensures Sorted(t,0,n-1);
  @*/
void insert_sort(int t[], int n) {
  int i,j;
  int mv;
  if (n <= 1) return;
  /*@ loop invariant 0 <= i <= n;
    @ loop invariant Sorted(t,0,i);
    @ loop variant n-i;
    @*/
  for (i=1; i<n; i++) {
    // assuming t[0..i-1] is sorted, insert t[i] at the right place
    mv = t[i]; 
    /*@ loop invariant 0 <= j <= i;
      @ loop invariant j == i ==> Sorted(t,0,i);
      @ loop invariant j < i ==> Sorted(t,0,i+1);
      @ loop invariant \forall integer k; j <= k < i ==> t[k] > mv;
      @ loop variant j;
      @*/
    // look for the right index j to put t[i]
    for (j=i; j > 0; j--) {
      if (t[j-1] <= mv) break;
      t[j] = t[j-1];
    }
    t[j] = mv;
  }
}


/*
Local Variables:
compile-command: "make insertion_sort.why3ide"
End:
*/
