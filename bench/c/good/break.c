/**************************************************************************/
/*                                                                        */
/*  The Why platform for program certification                            */
/*                                                                        */
/*  Copyright (C) 2002-2010                                               */
/*                                                                        */
/*    Yannick MOY, Univ. Paris-sud 11                                     */
/*    Jean-Christophe FILLIATRE, CNRS                                     */
/*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           */
/*    Romain BARDOU, Univ. Paris-sud 11                                   */
/*    Thierry HUBERT, Univ. Paris-sud 11                                  */
/*                                                                        */
/*  Secondary contributors:                                               */
/*                                                                        */
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

/* break tests */


/*@ ensures \result == 12 */
int f1()
{
  /*@ invariant \true variant 1 */ while (1) break;
  return 12;
}


/*@ ensures \result == 1 */
int f2() 
{
  int n = 10;
  
  /*@ invariant 0 <= n variant n */ 
  while (n >= 0) { 
    if (n == 0) { n++; break; }
    n--;
  }
  return n;
}
    

/*@ ensures \result == 2 */
int f3() 
{
  int n = 10;
  /*@ invariant 1 <= n variant n */
  while (n >= 0) { 
    if (n == 1) { n++; break; }
    n--;
  }
  return n;
}
    
/*@ ensures \result == 3 */
int f4(int x) 
{ 
  int i = 0;
  /*@ invariant i <= 3 variant 10 - i */
  for (i = 0; i < 10; i++) { 
    if (i == 3) break;
  }
  return i;
}

