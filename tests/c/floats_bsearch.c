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

#pragma JessieFloatModel(full)

/*@ predicate sorted{L}(double *t, integer a, integer b) =
  @    \forall integer i,j; a <= i <= j <= b ==> \le_float(t[i],t[j]);
  @*/

/*@ requires n >= 0 && \valid_range(t,0,n-1);
  @ requires ! \is_NaN(v);
  @ requires \forall integer i; 0 <= i <= n-1 ==> ! \is_NaN(t[i]);
  @ ensures -1 <= \result < n;
  @ behavior success:
  @   ensures \result >= 0 ==> \eq_float(t[\result],v);
  @ behavior failure:
  @   assumes sorted(t,0,n-1);
  @   ensures \result == -1 ==>
  @     \forall integer k; 0 <= k < n ==> \ne_float(t[k],v);
  @*/
int binary_search(double t[], int n, double v) {
  int l = 0, u = n-1;
  /*@ loop invariant
    @   0 <= l && u <= n-1;
    @ for failure:
    @   loop invariant
    @     \forall integer k;
    @      0 <= k < l ==> \lt_float(t[k],v);
    @   loop invariant
    @     \forall integer k;
    @      u < k <= n-1 ==> \lt_float(v,t[k]);
    @ loop variant u-l;
    @*/
  while (l <= u ) {
    int m = l + (u - l) / 2;
    //@ assert l <= m <= u;
    if (t[m] < v) l = m + 1;
    else if (t[m] > v) u = m - 1;
    else
      return m;
  }
  return -1;
}

/*
Local Variables:
compile-command: "make floats_bsearch.why3ide"
End:
*/
