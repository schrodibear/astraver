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

/*@ ensures x==4 => \result==2 */
int f1 (int x){
  int y ;
  
  switch (x) {
  case 0 :
  case 1 : 
    y=1 ;
    y=4;
    break;
  case 2:
  case 4:
    y=2; break;
  case 3:
    y=3; break;
  default :
    y=4;
    y=5;
  }
  return y;
}

/*@ ensures x==4 => \result==2 */
int f1a (int x){
  int y ;
  
  switch (x) {
  case 0 :
  case 1 : 
    y=1 ;
    y=4;
    break;
  case 2:
  case 4:
    y=2; return y;
  case 3:
    y=3; return y;
  default :
    y=4;
  }
  y=5;
  return y;
}

/*@ ensures \result==4 */
int f2 (int x){
  int y ;
  
  switch (x) {
  case 0 :
  case 1 : 
    y=1 ;
  case 2:
  case 4:
    y=2;
  case 3:
    y=3;
  default :
    y=4;
  }
  return y;
}

/*@ ensures \result==4 */
int f3 (int x){
  int y;

  switch (x) { 
  case 0 :
  case 1 : 
    y=1 ;
  default :
    y=2;
  case 3 :
    y=3;
  case 2 :
    y=4;
  }
  return y;
}

/*@ ensures \result==0 */
int f4 (int x){
  int y = 0;

  switch (x) { 
  case 0 :
    if (x==0) break ;
    y = 1;
  }
  return y;
}

/*@ ensures x==1 => \result==1 */
int f5 (int x){
  int y = 0;

  switch (x) { 
  case 1 :
    while (x>0) break ;
    y = 1;
  }
  return y;
}

/*@ ensures x==2 => \result==1 */
int f6 (int x){
  int y = 0;

  switch (x) { 
  case 1+1 :
    y = 1;
  }
  return y;
}

enum {A=5};

/*@ ensures x==A => \result==1 */
int f7 (int x){
  int y = 0;

  switch (x) { 
  case A :
    y = 1;
  }
  return y;
}

/*@ ensures x==0 && y>=1 => \result == 0
  @*/
int f8 (int x, int y){
  int z = 0;

  switch (x) { 
  case 0:
    if (y >= 1) break;
    z = 1;
    break;
  default: 
    z = 2;
  }
  return z;
}
