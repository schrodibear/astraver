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


/* contribution by Guillaume Melquiond */

// RUN GAPPA (does not work)

#pragma JessieFloatModel(defensive)

/*
 With some help, the Gappa tool is able to prove the postcondition of the
 sqrt function.

 First, it needs to know that Newton's iteration converges quadratically.
 This formula on relative errors is denoted by the newton_rel predicate.
 The newton states its general expression and it is proved by a short Coq
 script performing algebraic manipulations. The newton lemma is then
 instantiated by Alt-Ergo at each iteration of the loop to solve the
 three assertions about the predicate.

 In order to prove the postcondition, Gappa also needs to be told that
 the value computed after an iteration is close to both sqrt(x) and the
 value that would have been computed with an infinite precision. This is
 done by putting distance expressions into the context through three
 other assertions about the closeness predicate. They are much weaker
 than what Gappa will end up proving; they are only here to guide its
 heuristics.

 Finally, Gappa also needs to know about the inverse square root trick.
 That is what the assertion is for, and it is proved in Coq.
*/

/*@
 predicate newton_rel(real t, real x) =
   (0.5 * t * (3 - t * t * x) - 1/\sqrt(x)) / (1/\sqrt(x)) ==
     - (1.5 + 0.5 * ((t - 1/\sqrt(x)) / (1/\sqrt(x)))) *
     (((t - 1/\sqrt(x)) / (1/\sqrt(x))) * ((t - 1/\sqrt(x)) / (1/\sqrt(x))));

 lemma newton: \forall real t, x; x > 0. ==> newton_rel(t, x);

 predicate closeness(real u, real t, real x) =
   \abs(u - 0.5 * t * (3 - t * t * x)) <= 1 &&
   \abs(u - 1/\sqrt(x)) <= 1;
*/

/*@
 requires 0.5 <= x <= 2;
 ensures \abs(\result - 1/\sqrt(x)) <= 0x1p-6 * \abs(1/\sqrt(x));
*/
double sqrt_init(double x);

/*@
 requires 0.5 <= x <= 2;
 ensures \abs(\result - \sqrt(x)) <= 0x1p-43 * \abs(\sqrt(x));
*/
double sqrt(double x)
{
  double t, u;
  t = sqrt_init(x);

  u = 0.5 * t * (3 - t * t * x);
  //@ assert newton_rel(t, x);
  //@ assert closeness(u, t, x);
  t = u;

  u = 0.5 * t * (3 - t * t * x);
  //@ assert newton_rel(t, x);
  //@ assert closeness(u, t, x);
  t = u;

  u = 0.5 * t * (3 - t * t * x);
  //@ assert newton_rel(t, x);
  //@ assert closeness(u, t, x);
  t = u;

  //@ assert x * (1/\sqrt(x)) == \sqrt(x);
  return x * t;
}



/*
Local Variables:
compile-command: "make float_sqrt.why3ide"
End:
*/


