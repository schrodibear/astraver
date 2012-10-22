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

typedef unsigned int size_t;
void *malloc(size_t size);
void *calloc(size_t nmemb, size_t size);

typedef unsigned int uint;

#define DEFAULT 0

typedef struct SparseArray {
  int *val;
  uint *idx, *back;
  uint n;
  uint sz; // inutile ?
} *sparse_array;

/*@ predicate is_elt{L}(sparse_array a, integer i) =
  @      0 <= a->idx[i] < a->n
  @   && a->back[a->idx[i]] == i
  @ ;
  @*/

/*@ axiomatic Model {
  @   logic integer model{L}(sparse_array a,integer i);
  @   axiom model_in: \forall sparse_array a, integer i;
  @     is_elt(a,i) ==> model(a,i) == a->val[i];
  @   axiom model_out: \forall sparse_array a, integer i;
  @     !is_elt(a,i) ==> model(a,i) == DEFAULT;
  @}
  @*/

/*@ predicate inv(sparse_array a) =
  @   \valid(a) &&
  @   0 <= a->n <= a-> sz &&
  @   \valid(a->val+(0..a->sz-1)) &&
  @   \valid(a->idx+(0..a->sz-1)) &&
  @   \valid(a->back+(0..a->sz-1)) &&
  @   \forall integer i; 0 <= i < a->n ==>  
  @      0 <= a->back[i] < a->sz && a->idx[a->back[i]] == i;
  @*/


/*@ requires sz >= 0;
  @ assigns \nothing;
  @ ensures \fresh(\result,sizeof(struct Sparse_array));
  @ ensures inv(\result);
  @ ensures \result->sz == sz;
  @ ensures \forall integer i; model(\result,i) == DEFAULT;
  @*/
sparse_array create(uint sz) {
  sparse_array a = (sparse_array)malloc(sizeof(struct SparseArray));
  a->val = (int*)calloc(sz,sizeof(int));
  a->idx = (uint*)calloc(sz,sizeof(uint));
  a->back = (uint*)calloc(sz,sizeof(uint));
  a->n = 0;
  a->sz = sz; // inutile ?
  return a;
}

/*@ requires \valid(a);
  @ requires inv(a);
  @ requires i <= a->sz - 1;
  @ assigns \nothing;
  @ ensures \result == model(a,i);
  @*/
int get(sparse_array a, uint i) {
  // note: 0 <= a->idx[i] holds because of type uint
  //@ assert 0 <= a->idx[i];
  if (a->idx[i] < a->n && 
      a->back[a->idx[i]] == i) return a->val[i];
  else return 0;
}

/*@ requires \valid(a);
  @ requires inv(a);
  @ requires i <= a->sz - 1;
  @ assigns a->val[i],a->idx[..],a->back[..], a->n;
  @ ensures inv(a);
  @ ensures model(a,i) == v;
  @ ensures \forall integer j; j != i ==> 
  @    model(a,j) == \old(model(a,j)); 
  @*/
void set(sparse_array a, uint i, int v) {
  a->val[i] = v;
  if (!(a->idx[i] < a->n && a-> back[a->idx[i]] == i)) {
    //@ assert a->n < a->sz;
    a->idx[i] = a->n; a->back[a->n] = i; a->n++;
  }
}



int main() {
  sparse_array a = create(10), b = create(20);
  int x,y;
  x = get(a,5); y = get(b,7);
  //@ assert x == 0 && y == 0;
  set(a,5,1); set(b,7,2);
  x = get(a,5); y = get(b,7);
  //@ assert x == 1 && y == 2;
  x = get(a,0); y = get(b,0);
  //@ assert x == 0 && y == 0;
  return 0;
}





/*
Local Variables:
compile-command: "make sparse_array2.why3ide"
End:
*/
