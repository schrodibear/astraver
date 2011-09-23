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

typedef struct { int t2[5]; int t2bis[5]; int *p2; } las2; 
typedef struct { int t1[5]; int t1bis[5]; int *p1; las2 * pp; } las; 

las u,v,w; 


/* 
invariant inv0: 
\forall las x; x.p1!=x.t1 && x.p1!=x.pp->t2 && x.t1!=x.pp->t2 && x.pp->p2!=x.t1 && x.pp->p2!=x.p1 
*/ 
/*@ 
invariant inv1: 
\forall las x,las y; 
&x!=&y => 
   \base_addr(x.p1) != \base_addr(y.t1) 
 &&  \base_addr(x.p1) != \base_addr(y.p1) 
 &&  \base_addr(x.p1) != \base_addr(y.pp->t2) 


 &&  \base_addr(x.pp) != \base_addr(y.pp) 


 &&  \base_addr(x.t1) != \base_addr(y.pp->t2) 
 &&  \base_addr(x.pp->t2) != \base_addr(y.pp->t2) 
*/ 


/*@ 
requires \valid (p) && \valid(p->p1) && \valid(p->pp) && \valid(p->t1) 
 && \valid_range(p->t1,0,5) && \valid_range(p->pp->t2,0,5) && \valid(p->pp->p2) 
assigns p->t1[0 .. 5],*p->p1,p->pp->t2[0 .. 5],*p->pp->p2 
ensures p->t1[1] == *p->p1 + p->pp->t2[1] + *p->pp->p2 
*/ 
void g(las * p); 


/*@ 
requires \forall las x; (&x==&u  || &x==&v  || &x==&w) 
 => \valid(x.p1) && \valid(x.pp) && \valid(x.pp->t2) && \valid_range(x.t1,0,5) && \valid_range(x.pp->t2,0,5) 
 && \valid(x.pp->p2) 
assigns 
u.t1[0 .. 5],*u.p1,u.pp->t2[0 .. 5],u.pp->p2, 
v.t1[0 .. 5],*v.p1,v.pp->t2[0 .. 5],v.pp->p2, 
w.t1[0 .. 5],*w.p1,w.pp->t2[0 .. 5],w.pp->p2 
ensures \forall las x; (&x==&u  || &x==&v  || &x==&w) 
 => x.t1[1] == *x.p1 + x.pp->t2[1] + *x.pp->p2 
*/ 
void f() 
{ int a = (u.t1[1] == *u.p1 + u.pp->t2[1] + *u.pp->p2); 
 g(&u); /*@ assert u.t1[1] == *u.p1 + u.pp->t2[1] + *u.pp->p2 */ 
 g(&v); /*@ assert u.t1[1] == *u.p1 + u.pp->t2[1] + *u.pp->p2 *//*@ assert v.t1[1] == *v.p1 + v.pp->t2[1] + *v.pp->p2 */ 
 g(&w); 
}
