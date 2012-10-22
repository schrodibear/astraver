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


//@ ensures \result == \max(x,y);
int max(int x, int y) {
  return (x <= y) ? y : x;
}


//@ ensures \result == \min(x,y);
int min(int x, int y) {
  return (x <= y) ? x : y;
}


//@ ensures \result == \max(x,y);
float fmax(float x, float y) {
  return (x <= y) ? y : x;
}


//@ ensures \result == \min(x,y);
float fmin(float x, float y) {
  return (x <= y) ? x : y;
}


//@ ensures \result == \max(x,y);
double dmax(double x, double y) {
  return (x <= y) ? y : x;
}


//@ ensures \result == \min(x,y);
double dmin(double x, double y) {
  return (x <= y) ? x : y;
}



/*
Local Variables:
compile-command: "make minmax.why3ide"
End:
*/

