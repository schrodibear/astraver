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

/* C tests with pointers */

/*@ requires \valid(x)
  @ assigns *x
  @ ensures *x == 1 && \result == 0 */
int f(int *x) {
  *x = 0;
  return (*x)++;
} 

/*@ requires \valid(x)
  @ ensures *x == 1 && \result == 1 */
int f2(int *x) {
  *x = 0;
  return ++(*x);
} 

int* r;


/*@ requires \valid(r)
  @ ensures *r == 1 */
int g() { 
  return f(r); 
}

/*@ ensures *r == 1 */
int g2() { 
  r = (int*)malloc(sizeof(int));
  return f(r); 
}

/*@ ensures \result == 1 */
int h() { int z; z = 0; return f(&z) + z; }


int t[5];

//@ requires \valid_index(t,2) ensures \result == 1 
int array1() {
  int * p;
  p = &t[2];
  return *p++ = 1;
}

/* pointers and structures */

struct S { int x; int y; } s;

//@ requires \valid(s)  ensures \result >= 1
int struct1(int n) { 
  int * p = &s.x;
  *p = 1;
  s.y = 2;
  return *p; 
}
