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
/*  License version 2.1, with the special exception on linking            */
/*  described in file LICENSE.                                            */
/*                                                                        */
/*  This software is distributed in the hope that it will be useful,      */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  */
/*                                                                        */
/**************************************************************************/

/*@ axiom times_0: \forall integer x; 0 * x == 0 */
/*@ axiom times_S: \forall integer d, integer x; (d+1) * x == d * x + x */

/*@ requires
  @   x >= 0 && y > 0
  @ ensures
  @   0 <= \result < y &&
  @   \exists integer d; x == d * y + \result
  @*/
int math_mod(int x, int y) {
  /*@ invariant 0 <= x && \exists integer d; \old(x) == d * y + x
    @ variant x
    @*/
  while (x >= y) x = x - y;
  return x;
}
