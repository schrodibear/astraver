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

/* check that t[0..n-1] only contains 0 */

/*@ requires n >= 0 && \valid_range(t,0,n) 
    ensures \result <=> \forall int i; 0<=i<n => t[i]==0 */
int all_zeros(int t[], int n) {
  /*@ invariant n <= \old(n) && \forall int i; n<=i<\old(n) => t[i]==0
      variant n */
  while (--n>=0 && !t[n]);
  return n < 0;
}

/*@ requires n >= 0 && \valid_range(t,0,n) 
    ensures \result <=> \forall int i; 0<=i<n => t[i]==0 */
int all_zeros_0(int t[], int n) {
  int k;
  /*@ invariant 0 <= k <= n && \forall int i; 0<=i<k => t[i]==0 variant n-k */
  for (k = 0; k < n; k++) if (t[k]) return 0;
  return 1;
}
