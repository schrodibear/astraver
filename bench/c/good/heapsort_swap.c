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

/* Heapsort */

#include "sorting.h"

/*** heap property ***********************************************************/

/*@ predicate Hnode(int* a, int i, int h) {
  @   (2*i+1 <= h => a[i] >= a[2*i+1]) &&
  @   (2*i+2 <= h => a[i] >= a[2*i+2]) 
  @ }
  @*/

/*@ predicate H(int* a, int l, int h) {
  @   \forall int i; l <= i <= h => Hnode(a, i, h)
  @ }
  @*/

//@ axiom H_init: \forall int* a, int l, int h; l <= h < 2*l+1 => H(a, l, h)

// @ axiom H_reduce: \forall int* a, int h; 0 < h => H(a, 0, h) => H(a, 1, h-1)

/*@ axiom H_max: 
  @   \forall int* a, int h; 
  @     H(a, 0, h) => \forall int i; 0 <= i <= h => a[0] >= a[i]
  @*/

/*** arith *******************************************************************/

//@ axiom div2_1 : \forall int i; 0 <= i => 0 <= i/2 <= i

//@ axiom div2_2 : \forall int i; 0 < i => 0 <= i/2 < i

//@ axiom div2_3 : \forall int i; 0 <= i => i-1 < 2*(i/2)+1

/*****************************************************************************/

/*@ requires \valid(a+i) && \valid(a+j)
  @ assigns  a[i], a[j]
  @ ensures  Swap(contents(a), \old(contents(a)), i, j)
  @*/
void swap(int* a, int i, int j) {
  int tmp = a[i];
  a[i] = a[j];
  a[j] = tmp;
}

/*@ requires 
  @   0 <= low <= high && \valid_range(a, low, high) && H(a, low+1, high)
  @ assigns  
  @   a[low..high]
  @ ensures  
  @   Permut(contents(a), \old(contents(a)), low, high) && H(a, low, high)
  @*/
void sift_down(int* a, unsigned int low, unsigned int high) {
  unsigned int i = low, child;
  /*@ invariant 
    @   low <= i <= high && 
    @   Permut(contents(a), \at(contents(a), init), low, high) &&
    @   (\forall int k; low <= k <= high => k != i => Hnode(a, k, high)) &&
    @   ((low < i && low <= (i-1)/2) => 
    @      ((2*i+1 <= high => a[(i-1)/2] >= a[2*i+1]) &&
    @       (2*i+2 <= high => a[(i-1)/2] >= a[2*i+2])))
    @ loop_assigns
    @   a[low..high]
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
  @   0 <= n && \valid_range(a, 0, n-1)
  @ ensures  
  @   Permut(contents(a), \old(contents(a)), 0, n-1) && Sorted(a, 0, n-1)
  @*/
void heapsort(int* a, unsigned int n) {
  unsigned int i;
  if (n <= 1) return;
  /*@ invariant 
    @   0 <= i < n && Permut(contents(a), \at(contents(a), init), 0, n-1) &&
    @   H(a, i, n-1)
    @ variant i
    @*/
  for (i = n/2; i >= 1; i--) sift_down(a, i-1, n-1);
  /*@ invariant 
    @   0 <= i < n && Permut(contents(a), \at(contents(a), init), 0, n-1) &&
    @   H(a, 0, i) && Sorted(a, i+1, n-1) &&
    @   \forall int k1, int k2; 0 <= k1 <= i => i < k2 < n => a[k1] <= a[k2]
    @ variant i
    @*/
  for (i = n-1; i >= 1; i--) { 
    swap(a, 0, i); 
    //@ assert H(a, 1, i-1)
    sift_down(a, 0, i-1); 
  }
}
