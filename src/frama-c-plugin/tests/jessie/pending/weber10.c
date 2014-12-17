/*@ axiomatic NbOcc {
@ // nb_occ(t,i,j,e) gives the number of occurrences of e in t[i..j]
@ // (in a given memory state labelled L)
@ logic integer nb_occ{L}(int* t, integer i, integer j,
@ int e);
@ axiom nb_occ_empty{L}:
@ \forall int *t, e, integer i, j;i > j ==> nb_occ(t,i,j,e) == 0;
@ axiom nb_occ_true{L}:
@ \forall int *t, e, integer i, j; i <= j && t[j] == e ==> nb_occ(t,i,j,e) == nb_occ(t,i,j-1,e) + 1;
@ axiom nb_occ_false{L}:
@ \forall int *t, e, integer i, j; i <= j && t[j] != e ==> nb_occ(t,i,j,e) == nb_occ(t,i,j-1,e);
@ }
@*/
 
/*@ axiomatic IS_permutation {
logic integer is_permutation{L1,L2}(int* t1, int* t2, integer n);
axiom is_permutation_occ{L1,L2}:
\forall int *t1, *t2, n, integer i; i < n ==>
nb_occ{L1}(t1,0,n-1,\at(t1[i],L1)) == nb_occ{L2}(t2,0,n-1,\at(t2[i],L2));
}
*/
 
 
/*@
requires 0 <= length;
requires \valid_range(array1, 0, length-1);
ensures is_permutation{Old,Here}(array1, array1, length);
*/
void permute_test(int* array1, int length){}

/* 
Local Variables:
compile-command: "LC_ALL=C make weber10"
End:
*/
