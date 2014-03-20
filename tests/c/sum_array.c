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

#pragma JessieIntegerModel(math)

/*@ axiomatic Sum {
  @   // sum(t,i,j) denotes t[i]+...+t[j-1]
  @   logic integer sum{L}(int *t, integer i, integer j)
  @        reads i,j,t, t[..] ;
  @   axiom sum1{L} :
  @     \forall int *t, integer i; sum(t,i,i) == 0;
  @   axiom sum2{L} :
  @     \forall int *t, integer i, j;
  @       sum(t,i,j+1) == sum(t,i,j) + t[j];
  @ }
  @*/

/*@ lemma sum3{L} :
  @     \forall int *t, integer i, j, k;
  @       i <= j <= k ==>
  @         sum(t,i,k) == sum(t,i,j) + sum(t,j,k);
  @*/

/*@ lemma sum_footprint{L} :
  @     \forall int *t1,*t2, integer i, j;
  @       (\forall integer k; i<=k<j ==> t1[k] == t2[k]) ==>
  @       sum(t1,i,j) == sum(t2,i,j);
  @*/

/*@ requires n >= 1 && \valid_range(t,0,n-1) ;
  @ ensures \result == sum(t,0,n);
  @*/
int test1(int t[],int n) {
  int i,s = 0;

  /*@ loop invariant 0 <= i <= n && s == sum(t,0,i);
    @ loop variant n-i;
  */
  for(i=0; i < n; i++)
  {
    s += t[i];
  }
  return s;
}


/*@ requires n >= 1 && \valid_range(t,0,n-1);
  @ assigns t[..];
  @ ensures sum(t,0,n) == \old(sum(t,0,n))+n;
  @*/
void test2(int t[],int n) {
  int i;
  /*@ loop invariant 0 <= i <= n &&
    @     sum(t,0,n) == \at(sum(t,0,n),Pre)+i;
    @ loop variant n-i;
    @*/
  for(i=0; i < n; i++)
  {
    //@ assert sum(t,0,n) == sum(t,0,i) + t[i] + sum(t,i+1,n);
    t[i] += 1;
    //@ assert sum(t,0,n) == sum(t,0,i) + t[i] + sum(t,i+1,n);
  }
}

/*
Local Variables:
compile-command: "make sum_array.why3ide"
End:
*/
