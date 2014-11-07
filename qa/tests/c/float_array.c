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

#define EPS1 0x1p-53
#define UPPER 0x1p0
#define n 10

//@ predicate bounded(real z, real bound) = \abs(z) <= bound;

double x;

/*@
  @ requires bounded(d, UPPER);
  @ requires \round_error(d) == 0;
  @
  @ ensures \abs(x - (d + 1.0)) <= EPS1;
  @ ensures \round_error(x) <= EPS1;
*/
void AffectDoubleDansX(double d) {
        x=d+1.0;
}

/*@
  @ requires \valid_range(X,0,n);
  @ requires bounded(d, UPPER);
  @ requires \round_error(d) == 0;
  @
  @ ensures \abs(X[1] - (d + 1.0)) <= EPS1;
  @ ensures \round_error(X[1]) <= EPS1;
  @ ensures \abs(X[2] - (d + 1.0)) <= EPS1;
  @ ensures \round_error(X[2]) <= EPS1;
*/
void AffectDoubleDansTab(double d, double X[]) {
        X[1]=d+1.0;
        X[2]=d+1.0;
        // assert X[1] == \round_double(\NearestEven,d+1.0);
}

/*@
  @ requires \valid_range(X,0,n);
  @ requires bounded(d, UPPER);
  @ requires \round_error(d) == 0;
  @
  @ ensures \abs(X[1] - (d + 1.0)) <= EPS1;
  @ ensures \round_error(X[1]) <= EPS1;
*/
void AffectDoubleDansTab1(double d, double X[]) {
        X[1]=d+1.0;
}

/*@
  @ requires \valid_range(X,0,n);
  @ requires bounded(d, UPPER);
  @ requires \round_error(d) == 0;
  @
  @ ensures \abs(X[0] - (d + 1.0)) <= EPS1;
  @ ensures \round_error(X[0]) <= EPS1;
*/
void AffectDoubleDansTab0(double d, double X[]) {
        X[0]=d+1.0;
        //@ assert X[0] == \round_double(\NearestEven,d+1.0);
        //@ assert \exact(X[0]) == d+1.0;
}
