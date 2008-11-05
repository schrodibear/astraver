/**************************************************************************/
/*                                                                        */
/*  The Why platform for program certification                            */
/*  Copyright (C) 2002-2008                                               */
/*    Romain BARDOU                                                       */
/*    Jean-Fran�ois COUCHOT                                               */
/*    Mehdi DOGGUY                                                        */
/*    Jean-Christophe FILLI�TRE                                           */
/*    Thierry HUBERT                                                      */
/*    Claude MARCH�                                                       */
/*    Yannick MOY                                                         */
/*    Christine PAULIN                                                    */
/*    Yann R�GIS-GIANAS                                                   */
/*    Nicolas ROUSSET                                                     */
/*    Xavier URBAIN                                                       */
/*                                                                        */
/*  This software is free software; you can redistribute it and/or        */
/*  modify it under the terms of the GNU Library General Public           */
/*  License version 2, with the special exception on linking              */
/*  described in file LICENSE.                                            */
/*                                                                        */
/*  This software is distributed in the hope that it will be useful,      */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  */
/*                                                                        */
/**************************************************************************/


/*@ ensures \result == 0
  @*/
int f1() {
  int x=0;
  goto l1;
  x=1;
 l1: return x;
}


/*@ ensures x == 0 => \result == 0
  @*/
int f2(int x) {
  if (x==0) goto l1;
  x=1;
 l1: return x;
}


/*@ ensures x == 9 <=> \result == 10
  @*/
int f3(int x) {
  if (x==0) goto l1;
  x++;
  if (x==10) goto l1;
  x=1;
 l1: return x;
}

  
/*@ ensures x == 0 => \result == 0
  @*/
int f4(int x) {
  if (x==0) goto l1;
 l2:  x++;
 l1: return x;
}
  
