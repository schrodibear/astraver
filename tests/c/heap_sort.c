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

#include "binary_heap.h"


/*@ requires len >= 0;
  @ requires \valid_range(arr,0,len-1);
  @ // assigns arr[..];
  @ ensures \forall integer i,j; 0 <= i <= j < len ==> arr[i] <= arr[j]; 
  @*/
void heap_sort(int *arr, uint len) {
  uint i;
  heap h = create(len);
  /*@ loop invariant 0 <= i <= len;
    @ loop variant len - i;
    @*/
  for (i = 0; i < len; ++i) insert(h,arr[i]);
  /*@ loop invariant 0 <= i <= len;
    @ loop variant len - i;
    @*/
  for (i = 0; i < len; ++i) arr[i] = extract_min(h);
}



void main() {
  int arr[] = {42, 13, 42};
  heap_sort(arr,3);
  //@ assert arr[0] <= arr[1] && arr[1] <= arr[2];
  //@ assert arr[0] == 13 && arr[1] == 42 && arr[2] == 42;
}

