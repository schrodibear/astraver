/**************************************************************************/
/*                                                                        */
/*  The Why platform for program certification                            */
/*                                                                        */
/*  Copyright (C) 2002-2014                                               */
/*                                                                        */
/*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud                   */
/*    Claude MARCHE, INRIA & Univ. Paris-sud                              */
/*    Yannick MOY, Univ. Paris-sud                                        */
/*    Romain BARDOU, Univ. Paris-sud                                      */
/*                                                                        */
/*  Secondary contributors:                                               */
/*                                                                        */
/*    Thierry HUBERT, Univ. Paris-sud  (former Caduceus front-end)        */
/*    Nicolas ROUSSET, Univ. Paris-sud (on Jessie & Krakatoa)             */
/*    Ali AYAD, CNRS & CEA Saclay      (floating-point support)           */
/*    Sylvie BOLDO, INRIA              (floating-point support)           */
/*    Jean-Francois COUCHOT, INRIA     (sort encodings, hyps pruning)     */
/*    Mehdi DOGGUY, Univ. Paris-sud    (Why GUI)                          */
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

// for N = 10
#define NMAX 10
#define NMAXR 10.0
#define B 0x1.1p-50

// for N = 100
// #define NMAX 100
// #define NMAXR 100.0
// #define B 0x1.02p-47


// for N = 1000
// #define NMAX 1000
// #define NMAXR 1000.0
// #define B 0x1.004p-44


/*@ axiomatic ScalarProduct {
  @   // exact_scalar_product(x,y,n) = x[0]*y[0] + ... + x[n-1] * y[n-1]
  @   logic real exact_scalar_product{L}(double *x, double *y, integer n)
  @       reads x[..], y[..];
  @   axiom A1{L}: \forall double *x,*y;
  @      exact_scalar_product(x,y,0) == 0.0;
  @   axiom A2{L}: \forall double *x,*y; \forall integer n ;
  @      n >= 0 ==>
  @        exact_scalar_product(x,y,n+1) == 
  @          exact_scalar_product(x,y,n) + x[n]*y[n];
  @ }
  @*/


/*@ lemma bound_int_to_real:
  @   \forall integer i; i <= NMAX ==> i <= NMAXR;
  @*/


/*@ requires 0 <= n <= NMAX;
  @ requires \valid(x+(0..n-1)) && \valid(y+(0.. n-1)) ;
  @ requires \forall integer i; 0 <= i < n ==>
  @          \abs(x[i]) <= 1.0 && \abs(y[i]) <= 1.0 ;
  @ ensures
  @    \abs(\result - exact_scalar_product(x,y,n)) <= n * B;
  @*/
double scalar_product(double x[], double y[], int n) {
  double p = 0.0;
  /*@ loop invariant 0 <= i <= n ;
    @ loop invariant \abs(exact_scalar_product(x,y,i)) <= i;
    @ loop invariant \abs(p - exact_scalar_product(x,y,i)) <= i * B;
    @ loop variant n-i;
    @*/
  for (int i=0; i < n; i++) {
    // bounds, needed by Gappa
    //@ assert \abs(x[i]) <= 1.0;
    //@ assert \abs(y[i]) <= 1.0;
    //@ assert \abs(p) <= NMAXR*(1+B) ;

  L:
    p = p + x[i]*y[i];

    // bound on the rounding errors in the statement above, proved by gappa
    /*@ assert \abs(p - (\at(p,L) + x[i]*y[i])) <= B;
     */

    // the proper instance of triangular inequality to show the main invariant
    /*@ assert
          \abs(p - exact_scalar_product(x,y,i+1)) <=
          \abs(p - (\at(p,L) + x[i]*y[i])) +
          \abs((\at(p,L) + x[i]*y[i]) -
               (exact_scalar_product(x,y,i) + x[i]*y[i])) ;
    */

    // a lemma to show the invariant \abs(exact_scalar_product(x,y,i)) <= i
    /*@ assert
      \abs(exact_scalar_product(x,y,i+1)) <=
         \abs(exact_scalar_product(x,y,i)) + \abs(x[i]) * \abs(y[i]);
    */

    // a necessary lemma, proved only by gappa
    //@ assert \abs(x[i]) * \abs(y[i]) <= 1.0;
  }
  return p;
}



/*
Local Variables:
compile-command: "make scalar_product.why3ide"
End:
*/


