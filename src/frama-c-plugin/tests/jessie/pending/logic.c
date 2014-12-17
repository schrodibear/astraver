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

/*@ logic int f1(int t[], int x) reads t[..]; */

/*@ axiom ax_f1 : \forall int t[], int x; f1(t,x) == t[x]; */

void test_f1() {
  int t[2];
  t[0] = 0;
  //@ assert f1(t,0) == 0;
}


/*@ logic int f2(int t[], int x) { t[x] } ; */

void test_f2() {
  int t[2];
  t[0] = 0;
  // @ assert f2(t,0) == 0;
}


/*@ predicate p1(int t[], int x, int v) reads t[..]; */

/*@ axiom ax_p1 : \forall int t[], int x, int v; p1(t,x,v) <==> t[x]==v; */

void test_p1() {
  int t[2];
  t[0] = 0;
  //@ assert p1(t,0,0);
}



/*@ predicate p2(int t[], int x, int v) { t[x]==v }; */

void test_p2() {
  int t[2];
  t[0] = 0;
  //@ assert p2(t,0,0);
}

/*
Local Variables:
compile-command: "make logic"
End:
*/
