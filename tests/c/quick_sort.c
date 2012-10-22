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

// RUNSIMPLIFY: will ask regtests to run Simplify on this program

#pragma JessieIntegerModel(math)

#include "sorting.h"

/*@ requires \valid(t+i) && \valid(t+j);
  @ assigns t[i],t[j];
  @ ensures Swap{Old,Here}(t,i,j);
  @*/
void swap(int t[], int i, int j) {
  int tmp = t[i];
  t[i] = t[j];
  t[j] = tmp;
}

// quick_rec sorts t[l..r]
/*@ requires \valid_range(t,l,r);
  @ decreases r-l;
  @ assigns t[l..r];
  @ behavior sorted:
  @   ensures Sorted(t,l,r+1);
  @ behavior permutation:
  @   ensures Permut{Old,Here}(t,l,r);
  @*/
void quick_rec(int t[], int l, int r) {
  int v,m,i;
  if (l >= r) return;
  v = t[l];
  m = l; 
  /*@ loop invariant 
    @   \forall integer j; l < j <= m ==> t[j] < v;
    @ loop invariant
    @   \forall integer j; m < j <  i ==> t[j] >= v;
    @ loop invariant  
    @   Permut{Pre,Here}(t,l,r);
    @ loop invariant t[l] == v && l <= m < i <= r+1;
    @ loop variant r-i;
    @*/
  for (i = l + 1; i <= r; i++) {
    if (t[i] < v) {
    L1:
      swap(t,i,++m);
      //@ assert Permut{L1,Here}(t,l,r);
    }
  }
  //@ assert l <= m <= r;
 L: swap(t,l,m);
  //@ assert Permut{L,Here}(t,l,r);
  quick_rec(t,l,m-1);
  quick_rec(t,m+1,r);
}

/*@ requires \valid_range(t,0,n-1);
  @ behavior sorted:
  @   ensures Sorted(t,0,n);
  @ behavior permutation:
  @   ensures Permut{Old,Here}(t,0,n-1);
  @*/
void quick_sort(int t[], int n) {
  quick_rec(t,0,n-1);
}


/*
Local Variables:
compile-command: "make quick_sort.why3ide"
End:
*/
