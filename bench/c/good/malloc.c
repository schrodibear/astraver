/********************************************************************************/
/*                                                                              */
/*  The Why platform for program certification                                  */
/*                                                                              */
/*  Copyright (C) 2002-2010                                                     */
/*                                                                              */
/*    Yannick MOY, Univ. Paris-sud 11                                           */
/*    Jean-Christophe FILLIATRE, CNRS                                           */
/*    Claude MARCHE, INRIA & Univ. Paris-sud 11                                 */
/*    Romain BARDOU, Univ. Paris-sud 11                                         */
/*    Thierry HUBERT, Univ. Paris-sud 11                                        */
/*                                                                              */
/*  Secondary contributors:                                                     */
/*                                                                              */
/*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)                */
/*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)              */
/*    Sylvie BOLDO, INRIA                 (floating-point support)              */
/*    Jean-Francois COUCHOT, INRIA        (sort encodings, hypothesis pruning)  */
/*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                             */
/*                                                                              */
/*  This software is free software; you can redistribute it and/or              */
/*  modify it under the terms of the GNU Lesser General Public                  */
/*  License version 2.1, with the special exception on linking                  */
/*  described in file LICENSE.                                                  */
/*                                                                              */
/*  This software is distributed in the hope that it will be useful,            */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of              */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                        */
/*                                                                              */
/********************************************************************************/

/*@ requires 
  @   n >= 1 
  @ ensures 
  @   \valid_range(\result,0,n-1) && 
  @   \forall int i; 0<=i<n => \valid(\result[i]) */
int** test(int n) { 
  int** t = (int**)malloc(n * sizeof(int*));
  int i;
  /*@ invariant 
    @   0 <= i <= n && \forall int k; 0<=k<i => \valid(t[k]) */
  for (i = 0; i < n; i++)
    t[i] = (int*)malloc(sizeof(int));
  return t;
}

//@ ensures \result == 0
int main() {
  int** t = test(10);
  t[3][0] = 0;
  // t[4][0] = 1;
  return t[3][0];
}
