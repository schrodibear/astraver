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

class NoCreditException0 extends Exception {

    static final long serialVersionUID = 0;

    NoCreditException0();

}

public class Purse0 {
    
    public int balance;

    //@ invariant balance_non_negative: balance >= 0;

    /*@ behavior created:
      @   ensures balance == 0;
      @*/
    public Purse0() {
	balance = 0;
    }

    /*@ requires s >= 0;
      @ behavior done:
      @   assigns balance;
      @   ensures balance == \old(balance)+s;
      @*/
    public void credit(int s) {
	balance += s;
    }

    /*@ requires s >= 0;
      @ behavior done:
      @   assigns balance;
      @   ensures s <= \old(balance) && balance == \old(balance) - s;
      @ behavior amount_too_large:
      @   assigns \nothing;
      @   signals (NoCreditException0) s > \old(balance) ;
      @*/
    public void withdraw(int s) throws NoCreditException0 {
	if (balance >= s) {
	    balance = balance - s;
	}
	else {
	    throw new NoCreditException0();
	}
    }

    /*@ // requires p1 != null && p2 != null && p1 != p2;
      @ behavior ok:
      @   assigns p1.balance,p2.balance;
      @   ensures \result == 0;
      @*/
    public static int test(Purse0 p1, Purse0 p2) {
	p1.balance = 0;
	p2.credit(100);
	return p1.balance;
    }


    /*@ requires p != null;
      @ behavior ok:
      @   assigns p.balance ;
      @   ensures \result <==> (\old(p.balance) >= 1000);
      @*/
    public static boolean test2(Purse0 p) {
	try {
	    p.withdraw(1000);
	    return true;
	}
	catch (NoCreditException0 e) { 
	    return false; 
	}
    }

    
}


/*
Local Variables: 
compile-command: "make Purse0.io"
End: 
*/
