
/**
Extract from
http://www.first.fraunhofer.de/fileadmin/FIRST/ACSL-by-Example.pdf
*/

#pragma SeparationPolicy(none)


typedef int bool;
#define false		((bool)0)
#define true		((bool)1)

typedef int value_type;

typedef int size_type; 




/*@
  predicate IsValidRange(value_type* a, integer n) =
    (0 <= n) && \valid_range(a, 0, n-1);
*/

/*@
  predicate
    IsEqual{A,B}(value_type* a, integer n, value_type* b) =
      \forall integer i; 0 <= i < n ==> 
        \at(a[i], A) == \at(b[i], B);
*/



/*@
  axiomatic ParentChildAxioms
  {
    predicate ParentChild(integer i, integer j);

    axiom ParentChild_1:
      \forall integer i, j; ParentChild(i, j) <==>
         0 <= i < j && (j == 2*i+1 || j == 2*i+2);

    axiom ParentChild_2:
      \forall integer i, j; ParentChild(i, j) <==>
        0 < j && i == (j-1)/2;
  }

  lemma ParentChild_3:
    \forall integer i; 0 < i ==>
      ParentChild((i-1)/2, i) && 0 <= (i-1)/2 < i;

  predicate IsHeap{L}(value_type* c, integer n) = 
    \forall integer i, j;
      j < n && ParentChild(i, j) ==> c[i] >= c[j];
*/

/*@
  predicate IsMaximum{L}(value_type* a, integer n, integer max) =
     \forall integer i; 0 <= i < n ==> a[max] >= a[i];

  predicate IsFirstMaximum{L}(value_type* a, integer max) =
    \forall integer i; 0 <= i < max ==> a[i] < a[max];
*/

/*@
  axiomatic CountAxiomatic
  {
    logic integer Count{L}(value_type* a, value_type v,
                           integer i, integer j) reads a[i..(j-1)];

    axiom Count0:
      \forall value_type *a, v, integer i,j;
        i >= j ==> Count(a, v, i, j) == 0;

    axiom Count1:
      \forall value_type *a, v, integer i, j, k;
        0 <= i <= j <= k ==> Count(a, v, i ,k) ==
                             Count(a, v, i, j) + Count(a, v, j, k);

    axiom Count2:
      \forall value_type *a, v, integer i;
        (a[i] != v ==> Count(a, v, i, i+1) == 0) &&
        (a[i] == v ==> Count(a, v, i, i+1) == 1);

  logic integer CountWithHole{L}(value_type* c, value_type v, integer i, integer h,  integer j) =
      Count{L}(c, v, i, h) + Count{L}(c, v, h+1, j);

  logic integer CountWithoutHole{L}(value_type* c, value_type v, integer i, integer h,  integer j) =
      Count{L}(c, v, i, h) + Count{L}(c, v, h, j);
  }

  lemma CountLemma: \forall value_type *a, v, integer i;
    0 <= i ==> Count(a, v, 0, i+1) ==
               Count(a, v, 0, i) + Count(a, v, i, i+1);
*/

/*@
  predicate
    Permutation{A,B}(value_type* c, size_type n) = 
      \forall value_type x; 
        Count{A}(c, x, 0, n) == Count{B}(c, x, 0, n);
*/

/*@
  requires 0 < n && IsValidRange(a, n);
  requires IsHeap(a, n);

  assigns \nothing;

  ensures \forall integer i; 0 <= i < n ==> a[0] >= a[i];
*/
void pop_heap_induction(const value_type* a, size_type n);


/*@
  requires 0 < n && IsValidRange(a, n);
  requires 0 <= parent < child < n;
  requires a[parent] == a[child];

  assigns \nothing;

  ensures \forall value_type x; 
    CountWithHole(a, x, 0, child, n) == CountWithHole(a, x, 0, parent, n);
*/
void pop_push_heap_copy(value_type* a, size_type n, size_type parent, size_type child);

#define INT_MAX			2147483647

/*@
   requires 0 < n <  (INT_MAX-2)/2;
   requires IsValidRange(a, n);
   requires IsHeap(a, n);

   assigns a[0..(n-1)];

   ensures IsHeap(a, n-1);
   ensures a[n-1] == \old(a[0]);
   ensures IsMaximum(a, n, n-1);
   ensures Permutation{Old, Here}(a, n);
*/
void pop_heap(value_type* a, size_type n);


void pop_heap(value_type* a, size_type n)
{
  //@ ghost pop_heap_induction(a,n);
  //@ assert \forall integer i; 0 < i < n ==> a[0] >= a[i];
  value_type tmp = 0, max = 0;
  size_type hole = 0;
  tmp = a[n-1];
  max  = a[0];
  /*@ assert \forall value_type x;
        CountWithHole(a,x,0,hole,n) == Count{Pre}(a,x,1,n);
  */
  /*@
     loop invariant 0 <= hole < n;
     loop invariant IsHeap(a,n-1);
     loop invariant \forall integer i; 0 <= i < n ==> a[i] <= max;
     loop invariant \forall integer i;
        hole < n-1 && ParentChild(i,hole) ==> a[i] >= tmp;
     loop invariant \forall value_type x;
        CountWithHole(a,x,0,hole,n) == Count{Pre}(a,x,1,n);
     loop invariant \at(a[n-1],Pre) == a[n-1];

     loop assigns a[0..hole],hole;
     loop   variant n - hole;
  */
  while (true)
  {
    size_type child = 2*hole + 2;
    if (child < n-1)
    {
      if (a[child] < a[child-1]) child--;
      //@ assert ParentChild(hole,child);
      if (a[child] > tmp)
      {
        //@ assert hole < n-1;
        a[hole] = a[child];
        //@ assert \at(a[n-1],Pre) == a[n-1];
        //@ ghost pop_push_heap_copy(a,n,hole,child);
        hole = child;
      }
      else break;
    }
    else
    {
      child = 2*hole + 1;
      if (child == n-2 && a[child] > tmp)
      {
        //@ assert hole < n-1;
        a[hole] = a[child];
        //@ assert \at(a[n-1],Pre) == a[n-1];
        //@ ghost pop_push_heap_copy(a,n,hole,child);
        hole = child;
      }
      break;
    }
  }
  /*@  assert \forall integer i;
    hole < n-1 && ParentChild(i,hole) ==> a[i] >= tmp;
  */

  a[hole] = tmp;
  /*@ assert \forall value_type x;
        CountWithHole(a,x,0,hole,n) == Count{Pre}(a,x,1,n);
  */
  //@ assert hole<n-1 ==> a[hole] ==tmp== \at(a[n-1],Pre) == a[n-1];
  /*@ assert \forall value_type x; hole < n-1 ==>
        Count(a,x,hole+1,(n-1)+1)==CountWithoutHole(a,x,hole+1,n-1,n);
  */

  /*@ assert \forall value_type x;
      (hole < n-1 ==> CountWithHole(a,x,0,hole,n) ==
        CountWithHole(a,x,0,hole,n-1) +  Count(a,x,n-1 ,(n-1)+1) ==
        CountWithoutHole(a,x,0,hole,hole+1) + Count(a,x,hole+1,n-1) ==
        CountWithoutHole(a,x,0,hole,n-1) ==
        Count(a,x,0,n-1)) &&
      (hole == n-1 ==> CountWithHole(a,x,0,hole,n) ==
        CountWithHole(a,x,0,n-1,n) == Count(a,x,0,n-1));
  */
  /*@ assert \forall value_type x; Count(a,x,0,n-1) ==
        CountWithHole(a,x,0,hole,n) == Count{Pre}(a,x,1,n);
  */

  a[n-1]  = max;
  /*@ assert \forall value_type x;
        Count(a,x,n-1,(n-1)+1) == Count{Pre}(a,x,0,1);
  */
  /*@ assert \forall value_type x; CountWithoutHole(a,x,0,n-1,n) 
        == CountWithoutHole{Pre}(a,x,0,1,n);
  */
  /*@ assert \forall value_type x;
        Count(a,x,0,n) == CountWithoutHole(a,x,0,n-1,n) ==
        CountWithoutHole{Pre}(a,x,0,1,n) == Count{Pre}(a,x,0,n);
  */
}



void pop_heap_induction(const value_type* a, size_type n)
{
  /*@
  loop invariant 0 <= i <= n;
  loop invariant  \forall integer j;
     0 <= j < i <= n ==> a[0] >= a[j];
  loop   variant n - i;
  */
  for (size_type i = 1; i < n; i++)
  {
    //@ assert 0 < i ==> ParentChild((i-1)/2, i);
  }
}



