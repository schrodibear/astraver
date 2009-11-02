#include "remove_copy_array.h"

int remove_copy_array (int* a, int length, int* b, int value )
{
    int i = 0;
    int j = 0;

    /*@
			loop invariant 0 <= i <= length;
			loop invariant j <= i;
			loop invariant 0 <= j <= length;
			
			loop assigns b[0 .. j-1];
			loop invariant \forall integer k;	! ( 0 <= k < j) ==> b[k] == \at(b[k],Pre);
			
			loop invariant \forall integer k; 0 <= k < j ==> b[k] != value;
		
		
			loop invariant j == spec_remove_copy{Pre,Here}(a, i-1, b, j-1, value);
		
    */
    for ( ; i < length; ++i) // < instead of !=
        if (a[i] != value)
        {
            b[j] = a[i];		
            ++j;					
        }
    return j;
}
