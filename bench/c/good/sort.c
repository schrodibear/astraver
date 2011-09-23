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

/* sort 4 integers */


void sort4_1() {
  int a, b, c, d;
  int tmp;
  if (a > b) { tmp = a; a = b; b = tmp; }
  if (c > d) { tmp = c; c = d; d = tmp; }
  if (a > c) { tmp = a; a = c; c = tmp; }
  if (b > d) { tmp = b; b = d; d = tmp; }
  if (b > c) { tmp = b; b = c; c = tmp; }
  /*@ assert a <= b <= c <= d */
}



/*@ requires \valid_range(t,0,4) 
    ensures t[0] <= t[1] <= t[2] <= t[3] */
void sort4_4(int t[]) {
  int tmp;
  if (t[0] > t[1]) { tmp = t[0]; t[0] = t[1]; t[1] = tmp; }
  if (t[2] > t[3]) { tmp = t[2]; t[2] = t[3]; t[3] = tmp; }
  if (t[0] > t[2]) { tmp = t[0]; t[0] = t[2]; t[2] = tmp; }
  if (t[1] > t[3]) { tmp = t[1]; t[1] = t[3]; t[3] = tmp; }
  if (t[1] > t[2]) { tmp = t[1]; t[1] = t[2]; t[2] = tmp; }
}


/* commented because of memory explosion */
#if 0
/*@ requires \valid(a) && \valid(b) && \valid(c) && \valid(d) &&
  @   a != b && a != c && a != d && b != c && b != d && c != d
  @ ensures *a <= *b <= *c <= *d */
void sort4_2(int *a, int *b, int *c, int *d) {
  int tmp;
  if (*a > *b) { tmp = *a; *a = *b; *b = tmp; }
  if (*c > *d) { tmp = *c; *c = *d; *d = tmp; }
  if (*a > *c) { tmp = *a; *a = *c; *c = tmp; }
  if (*b > *d) { tmp = *b; *b = *d; *d = tmp; }
  if (*b > *c) { tmp = *b; *b = *c; *c = tmp; }
}
#endif



/*@ predicate swap_ord(int a2,int b2,int a1,int b1) {
  @   (a1 <= b1 => (a2 == a1 && b2 == b1)) && 
  @   (a1 > b1 => (a2 == b1 && b2 == a1))
  @ }
  @*/

/*@ requires \valid(a) && \valid(b) && \valid(c) && \valid(d) &&
  @   a != b && a != c && a != d && b != c && b != d && c != d
  @ ensures *a <= *b <= *c <= *d */
void sort4_3(int *a, int *b, int *c, int *d) {
  int tmp;
  //@ assigns *a,*b,tmp ensures swap_ord( *a,*b,\old( *a),\old( *b))
  if (*a > *b) { tmp = *a; *a = *b; *b = tmp; }
  //@ assigns *c,*d,tmp ensures swap_ord( *c,*d,\old( *c),\old( *d))
  if (*c > *d) { tmp = *c; *c = *d; *d = tmp; }
  //@ assigns *a,*c,tmp ensures swap_ord( *a,*c,\old( *a),\old( *c))
  if (*a > *c) { tmp = *a; *a = *c; *c = tmp; }
  //@ assigns *b,*d,tmp ensures swap_ord( *b,*d,\old( *b),\old( *d))
  if (*b > *d) { tmp = *b; *b = *d; *d = tmp; }
  //@ assigns *b,*c,tmp ensures swap_ord( *b,*c,\old( *b),\old( *c))
  if (*b > *c) { tmp = *b; *b = *c; *c = tmp; }
}

