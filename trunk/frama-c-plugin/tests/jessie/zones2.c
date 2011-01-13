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

struct S{ int x[1]; int y [2];}s;

/*@ ensures s.x[0] == 1; */
void f (){
  s.x[0] = 1;
  s.y[1] = 2;
}


typedef struct T {
  struct S *p;
} T;

T *t,*u;


int g() {
  return t->p->x[0] + u->p->x[0];
}

/* 
Local Variables:
compile-command: "LC_ALL=C make zones2"
End:
*/
