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

/* continue tests */

/*@ ensures \result == 0 */
int f1()
{
  int n = 10;
  /*@ invariant 0 <= n variant n */ 
  while (n > 0) {
    if (n == 5) { n = 0; continue; }
    n--;
  }
  return n;
}

/*@ ensures \result == 10 */
int f2()
{
  int i = 17;
  /*@ invariant i <= 10 variant 10 - i */ 
  for (i = 0; i < 10; i++) {
    if (i == 5) { i = 6; continue; }
  }
  return i;
}

/*@ ensures \result == 7 */
int f3()
{
  int i;
  /*@ invariant i <= 7 && i != 6 variant 7 - i */ 
  for (i = 0; i < 6; i++) {
    if (i == 5) 
      { i = 6; continue; }
  }
  return i;
}

/*
int main(void) {
  printf("%d\n",f3());
  return 0;
}
*/

  
