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

/* test option --local-aliasing */

char name[200];
// invariant name_valid : \valid_range(name,0,99)
//@ invariant name_valid : \arrlen(name) >= 100

// requires \valid_range(buf,0,size-1) && 0 <= size <= 100
//@ requires \arrlen(buf) >= size && 0 <= size <= 100
int f(char* buf, int size) {
  int i;
  char* p = buf;
  char* q = name;
  /*@ invariant 0 <= size <= \old(size)
    @           && p-buf == \old(size)-size
    @           && q-name == \old(size)-size
    @*/
  while (size--) {
    *p++ = *q++;
  }
  if (q == name) return 1;
  --buf;
  /*@ invariant 0 <= i <= \old(size)
    @*/
  for (i = p-buf-2; i> 1; i--) {
    buf[i] += 2;
  }
  ++buf;
  return 0;
}

// requires \exists int i; i >= 0 && s[i] == 0 && \valid_range(s,0,i)
//@ requires 0 <= \strlen(s) < \arrlen(s)
int g(char* s) {
  char c;
  int count = 0;
  /* invariant \exists int i; i >= 0 && s[i] == 0 && \valid_range(s,0,i)
    */
  /*@ invariant 0 <= s-\old(s) <= \strlen(\old(s)) < \arrlen(\old(s))
   */
  while (c = *s++) {
    switch (c) {
    case '0':
    case '1':
      count += 1;
      break;
    case '2':
      count -= count;
      if (!*s++) s--;
//  case '3':
    default:
      ++count;
      if (!*s++) s--;
      if (!*s++) s--;
    }
  }
  return count;
}

int h(char* p, int s) {
  char *q = p+s;
  char *pp = p;
  char buf[100];
  char *b = buf;
  //@ assert b == buf
  pp++;
  //@ assert pp == p + 1
  ++b;
  //@ assert b == buf + 1
  if (p < q && buf < b) {
    int diff = (buf-b) + (pp-p);
    diff += (q-p);
    //p = malloc(100 * sizeof(char));
    p++;
    //@ assert pp == p
    pp++;
    //@ assert pp == p + 1
    q++;
    //@ assert pp + s == q + 1
    diff += (q-pp);
    q = (char*)malloc(100 * sizeof(char));
    p = pp;
    //@ assert pp == p
    diff += (p-pp);
    return diff;
  }
  return -1;
}

int main() {
  char buf[100];
  int r = f(buf,100);
  buf[99] = 0;
  r += g(buf);
  r += h(buf,100);
  return r;
}
