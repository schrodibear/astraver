/* Frama-C BTS 0030

Status: cannot reproduce

*/



/*@
 requires 0 <= length_a;
 requires 0 <= length_b;


 requires \valid(a+ (0..length_a-1));
 requires \valid(b+ (0..length_b-1));
 
 assigns \nothing;

 ensures \result == 1 || \result == 0;
   
 ensures
 (
  (\exists integer k1; (0 <= k1 < length_a && 0 <= k1 < length_b) &&
    a[k1] < b[k1]) ||
    (\forall integer k2; (0 <= k2 < length_a) ==>
    length_a < length_b && a[k2] == b[k2])
 ) ^^ \result ==0 ;

*/
int lexicographical_compare_array (int* a, int length_a, int* b, int length_b)
{
    int i = 0;
    /*@
    loop invariant 0 <= i <= length_a;
    loop invariant 0 <= i <= length_b;
        
    loop invariant \forall integer k; 0 <= k < i ==> a[k] == b[k];
    */
    for ( ; i != length_a && i != length_b; ++i)
    {
        if (a[i] < b[i])
        {
                        /*@
                            assert \exists integer k1; 0 <= k1 <= i && a[k1] < b[k1];
    
                        */
            return 1;
        }
        if (b[i] < a[i])
        {
        
            return 0;
        }

    }
    //return i == length_a && i != length_b ? 1 : 0;
    
    if (i == length_a && i != length_b)
    {
            /*@
                assert
                (
  (\exists integer k1; (0 <= k1 < length_a && 0 <= k1 < length_b) &&
    a[k1] < b[k1]) ||
    (\forall integer k2; (0 <= k2 < length_a) ==>
    length_a < length_b && a[k2] == b[k2])
 );
            */
            return 1;
        }
        else
        {
            return 0;
        }
}



/* 
Local Variables:
compile-command: "LC_ALL=C frama-c -jessie bts0030.c"
End:
*/
