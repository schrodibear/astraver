/**************************************************************************/
/*                                                                        */
/*  The Why platform for program certification                            */
/*                                                                        */
/*  Copyright (C) 2002-2014                                               */
/*                                                                        */
/*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud                   */
/*    Claude MARCHE, INRIA & Univ. Paris-sud                              */
/*    Yannick MOY, Univ. Paris-sud                                        */
/*    Romain BARDOU, Univ. Paris-sud                                      */
/*                                                                        */
/*  Secondary contributors:                                               */
/*                                                                        */
/*    Thierry HUBERT, Univ. Paris-sud  (former Caduceus front-end)        */
/*    Nicolas ROUSSET, Univ. Paris-sud (on Jessie & Krakatoa)             */
/*    Ali AYAD, CNRS & CEA Saclay      (floating-point support)           */
/*    Sylvie BOLDO, INRIA              (floating-point support)           */
/*    Jean-Francois COUCHOT, INRIA     (sort encodings, hyps pruning)     */
/*    Mehdi DOGGUY, Univ. Paris-sud    (Why GUI)                          */
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


void buildMaze(uint n) {

  union_find u = create(n*n);

  //@ ghost integer num_edges = 0;

  /*@ loop invariant num_edges + NumClasses(u) == n*n;
    @*/
  while (num_classes(u) > 1) {
    uint x = rand() % n;
    uint y = rand() % n;
    uint d = rand() % 2;
    uint w = x, z = y;
    id (d == 0) w++; else z++;
    if (w < n && z < n) {
      int a = y*n+x, b = w*n+z;
      if (find(u,a) != find(u,b)) {
	// output_edge(x,y,w,z);
	//@ ghost num_edges++;
	union(a,b);
      }
    }
  }
  // nombre d'aretes = n*n - 1
  //@ assert num_edges == n*n - 1

  // each node is reachable from origin
  //@ assert \forall int x; 0 <= x < n*n ==> same(u,x,0);
}



