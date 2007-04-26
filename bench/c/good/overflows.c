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

/* integer arithmetic overflows (requires --int-overflow) */

/* operations */

/*@ ensures \result == 2 */
int add1() {
  unsigned char uc = 1;
  signed short s = 1;
  return uc + s;
}

/*@ requires x <= 1000
    ensures \result == x+1 */
int add2(int x) {
  return x+1;
}

int lsl() { return 1<<2; }

/* comparisons */

int cmp1() { return 1<2; }

/*@ ensures \result == 0 */
int not1() { signed char c = 1; return !c; }

/* constants */
void constant1() { int x = 1; }

/* incrementation */

void incr1() {
  unsigned char c = 254;
  c++;
  /*@ assert c == 255 */
}

unsigned short us;

/*@ requires us == 13 ensures us == 15 */
void incr2() { us++; ++us; }

/* casts */

void cast1() { 
  char c = 1;
  unsigned char uc = c;
}

/* arrays */

int t[10];

void array1() {
  signed char c = 1;
  t[c] = 0;
  t[c+1] = 0;
}

/*@ requires t[0] <= 1000 */
void incr3() {
  t[0]++;
}

/* structures */

struct S {
  unsigned char uc;
  signed char c;
  int i;
} s;

/*@ requires s.c == 0
    ensures  s.c == 3 && \result == 2 */
int struct1() { ++s.c; s.c++; return s.c++; }

/*
Local Variables: 
compile-command: "make overflows.overflows"
End: 
*/
