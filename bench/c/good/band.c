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

short ValueA;
/*@ invariant tev: 0 <= ValueA <= 10*/
short ValueB;
/*@ invariant ev: 0 <= ValueB <= 10*/
short returnValue;
/*@ invariant eev: 0 <= returnValue <= 10*/


/*@ 
  @ assigns returnValue
  @ ensures \result >= 0
  */
short test1(void)
{	
	returnValue = ValueA & ValueB;

	return returnValue;
}

/*@ 
  @ assigns returnValue
  @ ensures \result >= 0
  */
short test2(void)
{	
	returnValue = ValueA & ValueB;

	if((returnValue < 0) || (returnValue > 10))
	{
		returnValue = 0;
	}
	
	return returnValue;
}

/*@ 
  @ assigns returnValue
  @ ensures \result >= 0
  */
short test3(void)
{	
	returnValue = returnValue;

	return returnValue;
}

