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


typedef struct{int * p2;} las;

int f3(  las*  p1,  int*  p2); 

/*@ requires \valid(p1);
  @ ensures \result == 0; 
  @*/ 
int f3(  las*  p1,  int*  p2) 
{ 
  p1->p2 = p2; 
  return ( 0 ); 
}




typedef struct st {  int p;} st; 
/* ... */ 
void f4(  int*  p);
/* ... */ 
void f4(  int*  p){}

/*@ requires \valid(p);*/ 
void f4(  int*  p); 

/* 
Local Variables:
compile-command: "LC_ALL=C make clash_redef"
End:
*/
