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

/****** abstract sets of integers *******************************************/

//@ type iset

//@ predicate in_(int x, iset s)

//@ logic int card(iset s)
//@ axiom card_nonneg : \forall iset s; card(s) >= 0

//@ logic iset empty()
//@ axiom empty_card : \forall iset s; card(s)==0 <=> s==empty()

//@ logic iset remove(int x, iset s)
/*@ axiom remove_card : 
  @   \forall iset s; \forall int i;
  @     in_(i,s) => card(remove(i,s)) == card(s) - 1
  @*/

//@ logic int min_elt(iset s)
/*@ axiom min_elt_def : 
  @   \forall iset s; card(s) > 0 => in_(min_elt(s), s)
  @*/

/****** interpretation of C ints as abstract sets of integers ***************/

//@ logic iset iset(int x)

//@ axiom iset_c_zero : \forall int x; iset(x)==empty() <=> x==0

/*@ axiom iset_c_minus : 
  @   \forall int x, int a; 
  @     in_(x, iset(a)) => iset(a-x) == remove(x, iset(a))
  @*/

/*@ axiom iset_c_lowest_bit :
  @   \forall int x; x != 0 => x&-x == min_elt(iset(x))
  @*/
/*@ axiom iset_c_lowest_bit_help :
  @   \forall int x; x != 0 <=> x&-x != 0
  @*/

/**** count_bits ************************************************************/

/*@ ensures \result == card(iset(x)) */
int count_bits(int x) {
  int d, c;
  /*@ invariant c + card(iset(x)) == card(iset(\at(x,init)))
    @ variant   card(iset(x))
    @*/
  for (c = 0; d = x&-x; x -= d) c++;
  return c;
}
