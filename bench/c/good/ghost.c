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


int x;

/*@ ghost int pre_x = x */

/*@ ensures pre_x == \old(x) */
int f() {
  /*@ set pre_x = x */
  return x++;
}

/******** ghost arrays *******/

/*@ ghost int t[] */

int u[5];

/*@ ensures u[0] == \old(u[0]) && t[0] == 3 */
void g (){
  u[1]= 3;
  /*@set t[0] = u[1]*/
}


typedef struct S {
  int a;
  int b;
} S;



/*@ghost S tab[]*/

/*@ensures tab[0].a == 1*/
void h (){
  struct S a ;
  a.a = 1;
  /*@set tab[0] = a*/
}

/*@ ghost S s */


/*@ ensures s.a == 1*/
void i (){
  struct S a ;
  a.a = 1;
  /*@set s = a*/
}




/*
Local Variables: 
compile-command: "make ghost.gui"
End: 
*/
