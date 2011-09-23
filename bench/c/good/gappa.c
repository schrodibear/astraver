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

/*@ requires 0 <= x <= 1
  @ ensures  0 <= \result <= 1
  @*/


double calcul_debile0(double x) {
  double a;
  a=1-x;
  return a*a*a*a*a*a*a*a*a*a*a*a;
}


/*@ requires 0 <= x <= 1 && \exact(x)==x
  @ ensures
  @   161 <= \result <= 276 &&
  @   \round_error(\result) <= 2^^(-50)*|\result|  
  @*/

double calcul_debile1(double x) {
  double a,b;
  a=2*x+3;
  b=x*x+55;
  /*@ assert 0 <= b */
  a=a*b-4;
  return a;
}

/*@ requires 0 <= x <= 2^^(-3) && \round_error(x) <= 2^^(-54) 
  @ ensures
  @   \round_error(\result) <= 2^^(-51)  
  @*/

double calcul_debile2(double x) {
  return 1+x*(1+x*(1/2+x/6));
}





/*@ ensures
  @   \result == 256*x 
  @      && \round_error(\result)== 256*\round_error(x)
  @*/

double calcul_debile3(double x) {
  int i;
  /*@ invariant 0 <= i <= 8
    @    &&  x==2^^i*\old(x)
    @ variant 8 - i */ 
  
  for (i=0; i<8;i++)
    x*=2;
  return x;
}


/*@ requires 0 <= x <= 0.9
  @*/
void boucle(double x) {
  /*@ invariant 0 <= x <= 0.9 */
  while (x >= 0.5) 
    x = x*x;
}

/*
Local Variables: 
compile-command: "make gappa && ../../../bin/why.byte --fp --why why/gappa.why && ../../../bin/why.byte --fp --gappa why/gappa.why"
End: 
*/

