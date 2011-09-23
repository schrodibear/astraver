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

int v; 
/*@ ghost int pre_v */ 
/*@ ghost int pre2_v */ 

/*@ 
assigns v 
ensures v==-\old(v) 
*/ 
void g(){ v = -v; } 


/*@ 
assigns v,pre_v,pre2_v 
*/ 
void f() 
{ 
  int n; 
  
  n=100; 
  /*@ set pre2_v = 5 */ 
  /*@ set pre_v = -5 */ 
  v=5; 
  
  
  /*@ 
    invariant 0<=n<=100 && (pre2_v > pre_v => pre_v < v) && (pre_v == -v) 
    loop_assigns v,pre_v,pre2_v 
    variant n 
  */ 
  while(n--) 
    { 
      /*@ set pre2_v = pre_v */ 
      /*@ set pre_v = v */ 
      g(); 
    } 
}
