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


//@ ensures \result >= 0
int any();

//@ type intpair // = (int,int)

//@ logic intpair pair(int x, int y) 

//@ predicate lexico(intpair p1, intpair p2)

/* @ predicate lexico(intpair p1, intpair p2) = 
   @ \let (px1,py1) = p1 in ...
   @*/

/*@ axiom lexico_1 : \forall int x1, int x2, int y1, int y2; 
  @    x1 < y1 => lexico(pair(x1,x2),pair(y1,y2))
  @*/

/*@ axiom lexico_2 : \forall int x1, int x2, int y1, int y2; 
  @    x1 == y1 && x2 < y2 => lexico(pair(x1,x2),pair(y1,y2))
  @*/


//@ requires x >= 0 && y >= 0
int f(int x,int y) {

  /*@ invariant x >= 0 && y >= 0
    @ variant pair(x,y) for lexico
    @*/
  while (x > 0 && y > 0) {
    
    if (any()) {
      x--; y = any();
    }
    else y--;
    
  }

}
  
