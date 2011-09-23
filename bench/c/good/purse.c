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

typedef struct purse {
  int balance;
} purse;

//@ predicate purse_inv(purse *p) { \valid(p) && p->balance >= 0 }

/*@ requires purse_inv(p) && s >= 0
  @ assigns p->balance
  @ ensures purse_inv(p) && p->balance == \old(p->balance) + s 
  @*/
void credit(purse *p,int s) {
  p->balance = p->balance + s;
}



/*@ requires purse_inv(p) && 0 <= s <= p->balance
  @ assigns p->balance
  @ ensures purse_inv(p) && p->balance == \old(p->balance) - s
  @*/
void withdraw(purse *p,int s) {
  p->balance = p->balance - s;
}


/*@ requires purse_inv(p1) && purse_inv(p2) && p1 != p2
  @ assigns p1->balance, p2->balance
  @ ensures \result == 0
  @*/
int test1(purse *p1, purse *p2) {
    p1->balance = 0;
    credit(p2,100);
    return p1->balance;
}

/*@ assigns \nothing
  @ ensures \fresh(\result) && purse_inv(\result) && \result->balance == 0
  @*/
purse *new_purse() { 
  purse* p = (purse*) malloc(1 * sizeof(purse));
  p->balance = 0;
  return p;
}

/*@ ensures \result == 150
  @*/
int test2() {
  purse *p1 = new_purse();
  purse *p2 = new_purse();
  credit(p1,100);
  credit(p2,200);
  withdraw(p1,50);
  withdraw(p2,100);
  return p1->balance + p2->balance;
}


/*
void main() {
  purse *p = new_purse();
  test1(p,p);
}
*/
