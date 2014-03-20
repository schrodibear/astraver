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

/*@ requires \valid(p)
  @ assigns *p
  @ ensures *p == 1
  @*/
void g(int *p) {
  *p = 1;
}

int x = 45;

/*@ assigns x
  @ ensures x == 1
  @*/
void f1() {
  x = 1;
}

/*@ assigns x
  @ ensures x == 1
  @*/
void f2() {
  g(&x);
}

typedef struct{ int c1; int c2; } las;
las * plas; 

/*@ 
  @ requires \valid(plas) 
  @ assigns plas->c1,plas->c2 
  @ ensures plas->c1 == 1 && plas->c2 == 1
  @*/ 
void f4() 
{ 
  plas->c2 = 2; 
  g(&plas->c1); 
  g(&plas->c2); 
}



int t[3] = {1,2,3};

/*@ requires \valid(p) && \valid( *p)
  @ assigns **p
  @ ensures **p == 2
  @*/
void h(int **p) {
  **p = 2;
}

// mal typ‚ !
// /*@ requires t[1] == 2
//   @ ensures t[0] == 2 && t[1] == 2 */
// void f3() {
//   h(&t);
// }

