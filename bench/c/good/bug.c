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

/*@ axiom A : \forall double t[]; \forall int i; \valid(t+i) => t[i]>0.0 => t[i]>=0.0 */

typedef struct U { int t2[5]; int t2bis[5]; int *p2; } las2;
typedef struct V { int t1[5]; int t1bis[5]; int *p1; las2 * pp; } las;
las u,v,w;
las2 z;
las2 y1[5];
las2 y2[10];

/* predicate separation_intern_struct_U(las2* p) reads p->t2, p->t2bis */

/* axiom sep_U : 
  \forall las2 *p; \valid(p) => separation_intern_struct_U(p) */


/*@ requires \valid(x) */
void f(struct U *x) { x->t2[0] = 1; *u.p1 = 1; *z.p2 = 2; }

int ff(double a,double b)
{
int x;
x=(a<b);
return x;
}

//@ ensures \result < a
double f2(double a) { return (a - 1.2e-3); }
 
/*@ requires 0.0 < x <= 1.0
*/
void f3(double x)
{
/* ... */
x = x * 2.0;
/* ... */
}

typedef double arr[5];

/*@ requires \valid(d)
  @
  @*/
void f4(arr * d)
{
int i=0;
for(i=0;i<5;i++) (*d)[i]=i;
}

arr t;

void g4()
{ f4(&t); }
