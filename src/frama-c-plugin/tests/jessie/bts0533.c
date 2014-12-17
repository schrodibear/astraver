
/*

Alt-Ergo bug, should be fixed in Alt-Ergo 0.92

*/


/*@ requires \valid(array+(0..n-1));
    requires \forall integer i, j; 0 <= i < j < n ==> array[i] < array[j];
    behavior found:
      assumes \exists integer i; 0 <= i < n && array[i] == key ;
      ensures array[\result] == key;
    behavior notfound:
      assumes \forall integer i; 0 <= i < n ==> array[i] != key ;
      ensures \result == 4294967295UL;
*/
unsigned int bsearch(int key, int array[], unsigned int n) {
    if (n == 0) {
        return 4294967295UL;
    }
    //@ assert n > 0;

    if (array[0] == key) { return 0; }
    if (array[n-1] == key) { return n-1; }

    unsigned int left = 0;
    unsigned int right = n - 1;
    unsigned int diff = right - left;

    /*@ loop invariant \valid(array+(left..right));
        loop invariant left <= right;
        loop invariant diff == right - left;
        loop invariant \forall integer i; 0 <= i <= left ==> array[i] != key ;
        loop invariant \forall integer i; right <= i < n ==> array[i] != key ;
        loop variant diff;
    */
    while (diff > 0) { // FIXME: Change to diff > 1 
        unsigned int mid = left + (right - left) / 2;
        if (array[mid] == key) { return mid; }
        else if (array[mid] < key) {
            left = mid;
        } else {
            right = mid;
        }
        diff = right - left;
    }

    return 4294967295UL;
}

int main() {
    int array[] = { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9 };
    
    int i;
    /*@ loop variant 10 - i; */
    for (i = -1; i <= 10; ++i) {
      bsearch(i, array, 10);
      //printf("key=%d pos=%u\n", i, bsearch(i, array, 10));
    }
    return 0;
}
