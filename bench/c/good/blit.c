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

/*@ requires \valid_range(t, ofs1, ofs1+len-1) 
  @       && \valid_range(t, ofs2, ofs2+len-1)
  @       && 0 <= len
  @ ensures  \forall int i; 0 <= i < len => t[ofs2 + i] == \old(t[ofs1 + i])
  @*/
void blit(char *t, int ofs1, int ofs2, int len) {
  if (ofs1 == ofs2) return;
  if (ofs1 < ofs2)
    /*@ invariant 0 <= len <= \at(len, init)
      @        && \forall int i; len <= i < \at(len, init) => t[ofs2 + i] == \at(t[ofs1 + i], init)
      @ loop_assigns t[ofs2+len..ofs2+\at(len, init)-1]
      @ variant len
      @*/
    while (len-- > 0)
      t[ofs2 + len] = t[ofs1 + len];
  else 
    /*@ invariant 0 <= len <= \at(len, init)
      @        && ofs2 - \at(ofs2, init) == ofs1 - \at(ofs1, init) == \at(len, init) - len
      @        && \forall int i; 0 <= i < ofs2 - \at(ofs2, init) => 
      @                          t[\at(ofs2,init) + i] == \at(t[\at(ofs1, init) + i], init)
      @ loop_assigns t[\at(ofs2, init)..ofs2-1]
      @ variant len
      @*/
    while (len-- > 0)
      t[ofs2++] = t[ofs1++];
}
