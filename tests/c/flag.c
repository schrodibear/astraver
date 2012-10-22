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

/* Dijkstra's dutch flag */

#pragma JessieIntegerModel(math)

typedef char color;

#define BLUE (color)1
#define WHITE (color)2
#define RED (color)3

/*@ predicate is_color(color c) =
  @   c == BLUE || c == WHITE || c == RED ;
  @*/

/*@ predicate is_color_array{L}(color *t, integer l) =
  @   \valid_range(t,0,l-1) &&
  @   \forall integer i; 0 <= i < l ==> is_color(t[i]) ;
  @*/

/*@ predicate is_monochrome{L}(color *t,integer i, integer j, color c) =
  @   \forall integer k; i <= k < j ==> t[k] == c ;
  @*/


/*@ requires \valid_range(t,i,j);
  @ behavior decides_monochromatic:
  @   ensures \result <==> is_monochrome(t,i,j,c);
  @*/
int isMonochrome(color t[], int i, int j, color c) {
  /*@ loop invariant i <= k &&
    @   \forall integer l; i <= l < k ==> t[l] == c;
    @ loop variant j - k;
    @*/
  for (int k = i; k < j; k++) if (t[k] != c) return 0;
  return 1;
}

/*@ requires \valid_index(t,i);
  @ requires \valid_index(t,j);
  @ behavior i_j_swapped:
  @   assigns t[i],t[j];
  @   ensures t[i] == \old(t[j]) && t[j] == \old(t[i]);
  @*/
void swap(color t[], int i, int j) {
  color z = t[i];
  t[i] = t[j];
  t[j] = z;
}

/*@ requires l >= 0 && is_color_array(t, l);
  @ behavior sorts:
  @   ensures
  @     (\exists integer b,r;
  @        is_monochrome(t,0,b,BLUE) &&
  @        is_monochrome(t,b,r,WHITE) &&
  @        is_monochrome(t,r,l,RED));
  @*/
void flag(color t[], int l) {
  int b = 0;
  int i = 0;
  int r = l;
  /*@ loop invariant
    @   is_color_array(t,l) &&
    @   0 <= b <= i <= r <= l &&
    @   is_monochrome(t,0,b,BLUE) &&
    @   is_monochrome(t,b,i,WHITE) &&
    @   is_monochrome(t,r,l,RED);
    @ loop variant r - i;
    @*/
  while (i < r) {
    switch (t[i]) {
    case BLUE:
      swap(t,b++, i++);
      break;
    case WHITE:
      i++;
      break;
    case RED:
      swap(t,--r, i);
      break;
    }
  }
}



/*
Local Variables:
compile-command: "make flag.why3ide"
End:
*/
