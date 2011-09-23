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

/* Heapsort (safety only) */

/*** arith *******************************************************************/

//@ axiom div2_1 : \forall unsigned int i; 0 <= i => 0 <= i/2 <= i

//@ axiom div2_2 : \forall unsigned int i; 0 < i => 0 <= i/2 < i

// @ axiom div2_3 : \forall int i; 0 <= i => 2*(i/2) <= i

/*****************************************************************************/

/*@ requires \valid(a+i) && \valid(a+j)
  @*/
void swap(int* a, unsigned int i, unsigned int j) {
  int tmp = a[i];
  a[i] = a[j];
  a[j] = tmp;
}

/*@ requires 
  @   0 <= low <= high && 2*high <= \max_range(unsigned int) 
  @   && \valid_range(a, low, high)
  @*/
void sift_down(int* a, unsigned int low, unsigned int high) {
  unsigned int i = low, child;
  /*@ invariant 
    @   low <= i <= high
    @ variant 
    @   high - i
    @*/
  while ((child = 2*i+1) <= high) {
    if (child+1 <= high && a[child+1] >= a[child]) child++;
    if (a[i] >= a[child]) break;
    swap(a, i, child);
    i = child;
  }
}

/*@ requires 
  @   0 <= n  && 2*(n-1) <= \max_range(unsigned int) && \valid_range(a, 0, n-1)
  @*/
void heapsort(int* a, unsigned int n) {
  unsigned int i;
  if (n <= 1) return;
  /*@ invariant 
    @   0 <= i < n
    @ variant 
    @   i
    @*/
  for (i = n/2; i >= 1; i--) sift_down(a, i-1, n-1);
  /*@ invariant 
    @   0 <= i < n
    @ variant 
    @   i
    @*/
  for (i = n-1; i >= 1; i--) { swap(a, 0, i); sift_down(a, 0, i-1); }
}

/*
Local Variables: 
compile-command: "make heapsort_swap_safety.overflows"
End: 
*/
