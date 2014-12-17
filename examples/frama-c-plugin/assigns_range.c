/**************************************************************************/
/*                                                                        */
/*  The Why/Caduceus/Krakatoa tool suite for program certification        */
/*  Copyright (C) 2002-2006                                               */
/*    Jean-Fran�ois COUCHOT                                               */
/*    Mehdi DOGGUY                                                        */
/*    Jean-Christophe FILLI�TRE                                           */
/*    Thierry HUBERT                                                      */
/*    Claude MARCH�                                                       */
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

int t[10];

/*@ assigns t[0..3]; */
int f() {
  t[0] = t[1] = t[2] = t[3] = 0;
  return 0;
}


//@ assigns t[\at(\result,Post)]; 
int g() {
  t[2] = 9;
  return 2;
}
  
/*@ requires \valid(p) && \valid(q);
  @ assigns *q;
*/
int f1(int* p,int* q) { 
  p = q; *p = 1; return 1; 
}


typedef struct { int * rc; } S;
 
/*@
requires \valid(p)
  && \valid(p->rc)
  && \valid(r);
assigns *(\at(p->rc,Post)),p->rc;
*/
int f2(  S* p,int* r)
{
 p->rc = r;
 *(p->rc) = 55;
 return 1;
}


/* 
Local Variables:
compile-command: "LC_ALL=C make assigns_range"
End:
*/
