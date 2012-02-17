#ifndef _remove_copy_array_h
#define _remove_copy_array_h
#ifdef __cplusplus
extern "C"
{
#endif

    /*
     ======================================================================================
     DESCRIPTION:
      Copies the values of the elements in the range [first,last) to the range positions
      beginning at result, except for the elements that compare equal to value, which are
      not copied.
     Parameters:
      first, last:
       Pointers to the initial and final positions in a sequence. The range used is
       [first,last), which contains all the elements between first and last, including
       the element pointed by first but not the element pointed by last.
     b:
       Pointer to the initial position of the range where the resulting range of
       values is stored.
     value:
       Value to be removed.
     Return value:
      A pointer pointing to the end of the copied range, which includes all the elements
      in [first,last) except for those with a value of value.

     Complexity:
     Performs as many comparisons as the number of elements in the range [first,last),
     and at most as many assignment operatiodns.
     ======================================================================================


    */

/*@
    predicate disjoint_arrays(int* a, int* b, integer n) =
        \forall integer i, k;
            0 <= i < n && 0 <= k < n ==> a + i != b + k;
*/
/*@ axiomatic Specification_remove_copy {

		logic integer spec_remove_copy{La,Lb}(int* a, integer i, int* b, integer j, int value);

		axiom remove_copy_empty{La,Lb}:
		 \forall int* a, int* b, value, integer i, j;
		 0 > i || 0 > j ==> spec_remove_copy{La,Lb}(a, i, b, j, value) == 0;

		axiom remove_copy_equal_value{La,Lb}:
		\forall int* a, int* b, value, integer i, j;
			0 <= i && \at(a[i],La) == value ==>
			spec_remove_copy{La,Lb}(a, i, b, j, value) ==
			spec_remove_copy{La,Lb}(a, i-1, b, j, value);

		axiom remove_copy_not_equal_value{La,Lb}:
		\forall int* a, int* b, value, integer i, j;
			0 <= i && 0 <= j && (\at(a[i],La) != value <==>
			\at(a[i],La) == \at(b[j],Lb)) ==>
			spec_remove_copy{La,Lb}(a, i, b, j, value) ==
			spec_remove_copy{La,Lb}(a, i-1, b, j-1, value) + 1;

		axiom remove_copy_label{La,Lb1,Lb2}:
		 \forall int* a, int* b, value, integer i, j;
		 (\forall integer k; 0 <= k <= j ==>
				\at(b[k],Lb1) == \at(b[k],Lb2)) ==>
			 spec_remove_copy{La,Lb1}(a, i, b, j, value) ==
			 spec_remove_copy{La,Lb2}(a, i, b, j, value);
}
*/


/*@
	requires 0 <= length;
	requires \valid(a+(0..length-1));
	requires \valid(b+(0..length-1));

	assigns b[0 .. length-1];
	//assigns  b[0..\at(\result,Post)];
	//assigns refers to Pre-state, thus \result is unknown
	//over-approximated alternative: elements outside the range do not change

	ensures	\forall integer k;	! ( 0 <= k < \result) ==> b[k] == \old(b[k]);
	
	ensures 0 <= \result <= length;
	
	ensures \forall integer k; 0 <= k < \result ==> b[k] != value;

	ensures \result == spec_remove_copy{Old,Here}(a, length-1, b, \result-1, value);
*/
int remove_copy_array (int* a, int length, int* b, int value );


#ifdef __cplusplus
}
#endif
#endif
