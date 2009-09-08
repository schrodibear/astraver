/*@
  axiomatic Not_supported {
  predicate disjoint_arrays(int* a, int* b, integer length);
  // separated is not supported by jessie yet...
  // = \separated(a+(0..length-1),b+(0..length-1));
  }
*/

/*@ axiomatic Nb_occ {
  logic integer nb_occ{L}(int* a, integer fst, integer last, int value);
  axiom nb_occ_nil{L}:
  \forall int* a, integer fst, last, int value;
  last >= fst ==> nb_occ(a,fst,last,value) == 0;
  axiom nb_occ_head{L}:
  \forall int* a, integer fst, last, int value;
  fst < last && \valid(a+fst) && a[fst] == value ==>
  nb_occ(a,fst,last,value) == nb_occ(a,fst+1,last,value) + 1;
  axiom nb_occ_tail{L}:
  \forall int* a, integer fst, last, int value;
  fst < last && \valid(a+fst) && a[fst] != value ==>
  nb_occ(a,fst,last,value) == nb_occ(a,fst,last,value);
}
*/

/*@
requires 0 <= length;
requires \valid_range (a, 0, length-1);
requires \valid_range (dest, 0, length-1);
requires disjoint_arrays(a, dest, length);
ensures \result == length - nb_occ{Old}(a, 0, length, value);
ensures \forall integer k; 0 <= k < \result ==> dest[k] != value;

*/
int remove_copy_array (int* a, int length, int* dest, int value )
{
int index_a = 0;
int index_dest = 0;
/*@
loop invariant 0 <= index_a <= length;
loop invariant index_dest <= index_a;
loop invariant 0 <= index_dest <= length;

loop invariant \forall integer k; 0 <= k < index_dest ==> dest[k] != value;
loop invariant index_dest == index_a - nb_occ{Pre}(a, 0, index_a, value);

*/
for ( ; index_a != length; ++index_a)
if (a[index_a] != value)
{
dest[index_dest] = a[index_a];
++index_dest;
}
return index_dest;

}
