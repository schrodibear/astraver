/**************************************************************************/
/*                                                                        */
/*  The Why platform for program certification                            */
/*                                                                        */
/*  Copyright (C) 2002-2010                                               */
/*                                                                        */
/*    Jean-Christophe FILLIATRE, CNRS                                     */
/*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           */
/*    Yannick MOY, Univ. Paris-sud 11                                     */
/*    Romain BARDOU, Univ. Paris-sud 11                                   */
/*    Thierry HUBERT, Univ. Paris-sud 11                                  */
/*                                                                        */
/*  Secondary contributors:                                               */
/*                                                                        */
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


/*@ ensures \result == 0
  @*/
int f1() {
  int x=0;
  goto l1;
  x=1;
 l1: return x;
}


/*@ ensures x == 0 => \result == 0
  @*/
int f2(int x) {
  if (x==0) goto l1;
  x=1;
 l1: return x;
}


/*@ ensures x == 9 <=> \result == 10
  @*/
int f3(int x) {
  if (x==0) goto l1;
  x++;
  if (x==10) goto l1;
  x=1;
 l1: return x;
}

  
/*@ ensures x == 0 => \result == 0
  @*/
int f4(int x) {
  if (x==0) goto l1;
 l2:  x++;
 l1: return x;
}
  
