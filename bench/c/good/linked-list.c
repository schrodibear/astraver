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

typedef struct struct_list {
  int hd;
  struct struct_list * tl;
} *list;

#define NULL ((void*)0)

/*@ predicate is_list(list p) reads p->tl */

/*@ axiom is_list_def : 
     \forall list p; 
     is_list(p) <=> (p == NULL || (\valid(p) && is_list(p->tl))) */

/*@ logic int length(list p) reads p->tl */

/* @ axiom length_null : length((list)NULL) == 0 */

/*@ axiom length_nonneg : \forall list p; is_list(p) => length(p) >= 0 */

/*@ axiom length_cons : 
     \forall list p; 
     is_list(p) => p != NULL => length(p) == length(p->tl) + 1 */

/*@ requires is_list(p)
  @ ensures  \result != NULL => \result->hd == v
  @*/
list search(list p, int v) {
  /*@ invariant is_list(p)
      variant   length(p) */
  while (p != NULL && p->hd != v) p = p->tl;
  return p;
}
