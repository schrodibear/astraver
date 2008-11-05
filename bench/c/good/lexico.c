/**************************************************************************/
/*                                                                        */
/*  The Why platform for program certification                            */
/*  Copyright (C) 2002-2008                                               */
/*    Romain BARDOU                                                       */
/*    Jean-Fran�ois COUCHOT                                               */
/*    Mehdi DOGGUY                                                        */
/*    Jean-Christophe FILLI�TRE                                           */
/*    Thierry HUBERT                                                      */
/*    Claude MARCH�                                                       */
/*    Yannick MOY                                                         */
/*    Christine PAULIN                                                    */
/*    Yann R�GIS-GIANAS                                                   */
/*    Nicolas ROUSSET                                                     */
/*    Xavier URBAIN                                                       */
/*                                                                        */
/*  This software is free software; you can redistribute it and/or        */
/*  modify it under the terms of the GNU Library General Public           */
/*  License version 2, with the special exception on linking              */
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
  
