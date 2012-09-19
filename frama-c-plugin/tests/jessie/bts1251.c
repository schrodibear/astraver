/*@ predicate Sorted{L}(int *a, integer l, integer r) =
		\forall integer i,j; l <= i < j <= r ==> a[i] <= a[j];
 */

/*@ requires \valid(a+ (0..a_length-1)) && a_length >= 0;
	requires Sorted(a,0,a_length-1);
	assigns \nothing;
	behavior success:
		assumes \exists integer res; 0 <= res <= a_length-1 && a[res] == val;
		ensures 0 <= \result <= a_length-1	&&	a[\result] == val;
	behavior failure:
		assumes !(\exists integer res; 0 <= res <= a_length-1 && a[res] == val);
		ensures \result == -1;
	complete behaviors;
	disjoint behaviors;
 */
int bsearch(int a[], int a_length, int val) {
	int low, mid, high;

	low = 0; high = a_length-1;
	/*@ loop invariant 0 <= low && high <= a_length-1;
		loop invariant \forall integer i; 0 <= i < low  ==>  a[i] < val;
		loop invariant \forall integer i; high < i <= a_length-1  ==>  a[i] > val;
		loop assigns low, high, mid;
		loop variant high-low;
	*/
	while(low <= high) {
		mid = low + (high - low) / 2;
//		mid = (high + low) / 2;
		if (a[mid] < val) low = mid+1;
		else if(a[mid] > val) high = mid-1;
		else return mid;
	}
	return -1;
}



int main() {
	int a[6] = {1,3,4,6,8,19};
	int k = bsearch(a, 6, -8);
	// assert k == -1;
	return 0;
}
