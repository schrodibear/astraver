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

//@+ CheckArithOverflow = no

class NoCreditException extends Exception {

    public NoCreditException() { }

}

public class Purse {
    
    static NoCreditException noCreditException = new NoCreditException();

    private int balance;
    //@ invariant balance_positive: balance > 0;

    /*@ requires amount > 0;
      @ assigns balance;
      @ ensures balance == amount;
      @*/
    public Purse(int amount) {
        balance = amount;
    }

    /*@ requires s >= 0;
      @ assigns balance;
      @ ensures balance == \old(balance) + s;
      @*/
    public void credit(int s) {
        balance += s;
    }

    /*@ requires s >= 0;
      @ assigns balance;
      @ ensures s < \old(balance) && balance == \old(balance) - s;
      @ behavior amount_too_large:
      @   assigns \nothing;
      @   signals (NoCreditException) 
      @         s >= \old(balance) ;
      @*/
    public void withdraw(int s) throws NoCreditException {
        if (s < balance)
            balance = balance - s;
        else
            throw noCreditException;
    }


    /*@ requires p != null && s >= 0;
      @ behavior transfer_ok:
      @   ensures 
      @       balance == \old(balance) - s &&
      @       p.balance == \old(p.balance) + s &&
      @       \result == balance;
      @ behavior transfer_failed: 
      @   signals (NoCreditException) 
      @       balance == \old(balance) &&
      @       p.balance == \old(p.balance);
      @*/
    public int transfer_to(Purse p, int s) throws NoCreditException {
	p.credit(s);
	withdraw(s);
	return balance;
    }
	
}



/*
  Local Variables: 
  compile-command: "make Purse"
  End: 
*/
