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

/*@ logic int f1(int t[], int x) reads t[..] */

/*@ axiom ax_f1 : \forall int t[], int x; f1(t,x) == t[x] */

void test_f1() {
  int t[2];
  t[0] = 0;
  //@ assert f1(t,0) == 0
}


/*@ logic int f2(int t[], int x) { t[x] } */

void test_f2() {
  int t[2];
  t[0] = 0;
  // @ assert f2(t,0) == 0
}


/*@ predicate p1(int t[], int x, int v) reads t[..] */

/*@ axiom ax_p1 : \forall int t[], int x, int v; p1(t,x,v) <=> t[x]==v */

void test_p1() {
  int t[2];
  t[0] = 0;
  //@ assert p1(t,0,0)
}



/*@ predicate p2(int t[], int x, int v) { t[x]==v } */

void test_p2() {
  int t[2];
  t[0] = 0;
  //@ assert p2(t,0,0)
}
