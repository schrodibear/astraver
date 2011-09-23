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

//@ logic int num_of_pos(int i,int j,int t[]) reads t[i]

/*@ axiom num_of_pos_empty :
  @   \forall int i, int j, int t[];
  @       i > j => num_of_pos(i,j,t) == 0
  @*/
 
/*@ axiom num_of_pos_true_case :
  @   \forall int i, int j, int t[];
  @       i <= j && t[j] > 0 => 
  @         num_of_pos(i,j,t) == num_of_pos(i,j-1,t) + 1
  @*/

/*@ axiom num_of_pos_false_case :
  @   \forall int i, int j, int t[];
  @       i <= j && ! (t[j] > 0) => 
  @         num_of_pos(i,j,t) == num_of_pos(i,j-1,t)
  @*/

/*@ axiom num_of_pos_strictly_increasing:
  @   \forall int i, int j, int k, int l, int t[];
  @       j < k && k <= l && t[k] > 0 => num_of_pos(i,j,t) < num_of_pos(i,l,t)
  @*/

/*@ requires length >= 0 && \valid_range(t,0,length-1)
  @*/
void m(int t[], int length) {
  int count = 0;
  int i;
  int *u;

  /*@ invariant
    @    0 <= i && i <= length && 
    @    0 <= count && count <= i && 
    @    count == num_of_pos(0,i-1,t)  
    @ variant length - i
    @*/
  for (i=0 ; i < length; i++) {
    if (t[i] > 0) count++;
  }
  u = (int *)calloc(count,sizeof(int));
  count = 0;
  
  /*@ invariant
    @    0 <= i && i <= length && 
    @    0 <= count && count <= i && 
    @    count == num_of_pos(0,i-1,t)
    @ variant length - i
    @*/
  for (i=0 ; i < length; i++) {
    if (t[i] > 0) {
      u[count++] = t[i];
    }
  }
}

/*
Local Variables: 
compile-command: "make muller.nosep"
End: 
*/
