/********************************************************************************/
/*                                                                              */
/*  The Why platform for program certification                                  */
/*                                                                              */
/*  Copyright (C) 2002-2010                                                     */
/*                                                                              */
/*    Yannick MOY, Univ. Paris-sud 11                                           */
/*    Jean-Christophe FILLIATRE, CNRS                                           */
/*    Claude MARCHE, INRIA & Univ. Paris-sud 11                                 */
/*    Romain BARDOU, Univ. Paris-sud 11                                         */
/*    Thierry HUBERT, Univ. Paris-sud 11                                        */
/*                                                                              */
/*  Secondary contributors:                                                     */
/*                                                                              */
/*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)                */
/*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)              */
/*    Sylvie BOLDO, INRIA                 (floating-point support)              */
/*    Jean-Francois COUCHOT, INRIA        (sort encodings, hypothesis pruning)  */
/*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                             */
/*                                                                              */
/*  This software is free software; you can redistribute it and/or              */
/*  modify it under the terms of the GNU Lesser General Public                  */
/*  License version 2.1, with the special exception on linking                  */
/*  described in file LICENSE.                                                  */
/*                                                                              */
/*  This software is distributed in the hope that it will be useful,            */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of              */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                        */
/*                                                                              */
/********************************************************************************/

//@+ CheckArithOverflow = no

/*@ axiomatic NumOfPos {
  @  logic integer num_of_pos{L}(integer i,integer j,int t[]);
  @  axiom num_of_pos_empty{L} :
  @   \forall integer i j, int t[];
  @    i > j ==> num_of_pos(i,j,t) == 0;
  @  axiom num_of_pos_true_case{L} :
  @   \forall integer i j k, int t[];
  @       i <= j && t[j] > 0 ==> 
  @         num_of_pos(i,j,t) == num_of_pos(i,j-1,t) + 1;
  @  axiom num_of_pos_false_case{L} :
  @   \forall integer i j k, int t[];
  @       i <= j && ! (t[j] > 0) ==> 
  @         num_of_pos(i,j,t) == num_of_pos(i,j-1,t);
  @ }
  @*/

/*@ lemma num_of_pos_strictly_increasing{L} :
  @   \forall integer i j k l, int t[];
  @       j < k && k <= l && t[k] > 0 ==> 
  @       num_of_pos(i,j,t) < num_of_pos(i,l,t);
  @*/

public class Muller {

    /*@ requires t!=null;
      @*/
    public static int[] m(int t[]) {
	int count = 0;
	
	/*@ loop_invariant
	  @    0 <= i && i <= t.length && 
	  @    0 <= count && count <= i && 
	  @    count == num_of_pos(0,i-1,t) ; 
	  @ loop_variant t.length - i;
	  @*/
	for (int i=0 ; i < t.length; i++) if (t[i] > 0) count++;
	
	int u[] = new int[count];
	count = 0;
	
	/*@ loop_invariant
	  @    0 <= i && i <= t.length && 
	  @    0 <= count && count <= i && 
	  @    count == num_of_pos(0,i-1,t);
	  @ loop_variant t.length - i;
	  @*/
	for (int i=0 ; i < t.length; i++) {
	    if (t[i] > 0) u[count++] = t[i];
	}
	return u;
    }
    
}

/*
Local Variables: 
compile-command: "make Muller"
End: 
*/
