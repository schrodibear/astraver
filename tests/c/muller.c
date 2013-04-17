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

typedef unsigned int size_t;
void *malloc(size_t size);
void *calloc(size_t nmemb, size_t size);

/*@ axiomatic NumOfPos {
  @  logic integer num_of_pos{L}(integer i,integer j,int *t);
  @  axiom num_of_pos_empty{L} :
  @   \forall integer i, j, int *t;
  @    i >= j ==> num_of_pos(i,j,t) == 0;
  @  axiom num_of_pos_true_case{L} :
  @   \forall integer i, j, int *t;
  @       i < j && t[j-1] > 0 ==>
  @         num_of_pos(i,j,t) == num_of_pos(i,j-1,t) + 1;
  @  axiom num_of_pos_false_case{L} :
  @   \forall integer i, j, int *t;
  @       i < j && ! (t[j-1] > 0) ==>
  @         num_of_pos(i,j,t) == num_of_pos(i,j-1,t);
  @ }
  @*/


/*@ lemma num_of_pos_non_negative{L} :
  @   \forall integer i, j, int *t; 0 <= num_of_pos(i,j,t);
  @*/

/*@ lemma num_of_pos_additive{L} :
  @   \forall integer i, j, k, int *t; i <= j <= k ==>
  @       num_of_pos(i,k,t) == num_of_pos(i,j,t) + num_of_pos(j,k,t);
  @*/

/*@ lemma num_of_pos_increasing{L} :
  @   \forall integer i, j, k, int *t;
  @       j <= k ==> num_of_pos(i,j,t) <= num_of_pos(i,k,t);
  @*/

/*@ lemma num_of_pos_strictly_increasing{L} :
  @   \forall integer i, n, int *t;
  @       0 <= i < n && t[i] > 0 ==>
  @       num_of_pos(0,i,t) < num_of_pos(0,n,t);
  @*/

/*@ requires l >= 0 && \valid_range(t,0,l-1);
  @*/
int* m(int *t, int l) {
  int i, count = 0;
  int *u;

  /*@ loop invariant
    @    0 <= i <= l &&
    @    0 <= count <= i &&
    @    count == num_of_pos(0,i,t) ;
    @ loop variant l - i;
    @*/
  for (i=0 ; i < l; i++) if (t[i] > 0) count++;

  u = (int*)calloc(count,sizeof(int));
  count = 0;

  /*@ loop invariant
    @    0 <= i <= l &&
    @    0 <= count <= i &&
    @    count == num_of_pos(0,i,t);
    @ loop variant l - i;
    @*/
  for (int i=0 ; i < l; i++) {
    if (t[i] > 0) u[count++] = t[i];
  }
  return u;
}


/*
Local Variables:
compile-command: "make muller.why3ide"
End:
*/
