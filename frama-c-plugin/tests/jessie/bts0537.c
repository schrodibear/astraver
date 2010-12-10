/*@ predicate Sorted{L}(int *a, integer l, integer h) =
    \forall integer i; l <= i < h ==> a[i] <= a[i+1];
// \forall integer i,j; 0 <= i < j <= aLength-1 ==> a[i] <= a[j];
 */

/*@ requires Sorted(a,0,aLength-1);
    requires \valid(a+ (0..aLength-1)) && aLength >= 0;
    assigns \nothing;
    behavior success:
      assumes \exists integer res; 0 <= res <= aLength-1 && a[res] == val;
      ensures \result >= 0  &&  a[\result] == val;
    behavior failure:
      assumes !(\exists integer res; 0 <= res <= aLength-1 && a[res] == val);
      ensures \result == -1;
    complete behaviors;
    disjoint behaviors;
 */
int binary_search(int val, int a[], int aLength) {
  int low, mid, high;

  low = 0; high = aLength-1;
  /*@ loop invariant 0 <= low && high <= aLength-1;
      loop invariant \forall integer i; 0 <= i < low  ==>  a[i] < val;
      loop invariant \forall integer i; aLength-1  >= i > high  ==>  a[i] > val;
      // loop variant high-low;
  */
  while(low <= high) {
    mid = low + (high - low) / 2;
    if (a[mid] < val) low = mid+1;
    else if(a[mid] > val) high = mid-1;
    else return mid;
  }
  return -1;
}
