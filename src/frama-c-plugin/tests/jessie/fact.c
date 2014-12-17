/**************************************************************************/
/*                                                                        */
/*  The Why/Caduceus/Krakatoa tool suite for program certification        */
/*  Copyright (C) 2002-2006                                               */
/*    Jean-François COUCHOT                                               */
/*    Mehdi DOGGUY                                                        */
/*    Jean-Christophe FILLIÂTRE                                           */
/*    Thierry HUBERT                                                      */
/*    Claude MARCHÉ                                                       */
/*    Yannick MOY                                                         */
/*                                                                        */
/*  This software is free software; you can redistribute it and/or        */
/*  modify it under the terms of the GNU General Public                   */
/*  License version 2, as published by the Free Software Foundation.      */
/*                                                                        */
/*  This software is distributed in the hope that it will be useful,      */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  */
/*                                                                        */
/*  See the GNU General Public License version 2 for more details         */
/*  (enclosed in the file GPL).                                           */
/*                                                                        */
/**************************************************************************/

// the following pragma allows to ignore potential arithmetic overflow
#pragma JessieIntegerModel(exact)

/* the \prod ACSL construct is not yet supported by the Jessie plugin
 * the following inductive definition is a work-around
 */

// is_prod(a,b,n) true whenever n = prod_{i=a..b} i
/*@ inductive is_prod(integer a, integer b, integer n) {
  @   case is_prod_empty : 
  @      \forall integer a,b; a > b ==> is_prod(a,b,1);
  @   case is_prod_left : 
  @      \forall integer a,b,n; a <= b && is_prod(a,b-1,n) 
  @           ==> is_prod(a,b,b*n);
  @ }
  @*/

/*@ requires n >= 0;
  @ decreases n; 
  @ ensures is_prod(1,n,\result);
  @*/
int fact(int n) {
  if (n == 0) return 1;
  return n * fact(n-1);
}

/* 
Local Variables:
compile-command: "LC_ALL=C make fact"
End:
*/
