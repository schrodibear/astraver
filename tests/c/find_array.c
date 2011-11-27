/** from Julien Signoles' tutorial
 **/

/*@
  predicate sorted{L}(int* arr, integer length) =
  \forall integer i, j; 0 <= i <= j < length ==> arr[i] <= arr[j];

  predicate mem{L}(int elt, int* arr, integer length) =
  \exists integer i; 0 <= i <length && arr[i] == elt;
*/

/*@
  requires sorted(arr,length);
  requires length >= 0;
  requires \valid(arr+(0..(length-1)));

  assigns \nothing;

  behavior exists:
    assumes mem(query, arr, length);
    ensures arr[\result] == query;

  behavior not_exists:
    assumes ! mem(query, arr, length);
    ensures \result == -1;
*/
int find_array(int* arr, int length, int query) {
  int low = 0;
  int high = length - 1;
  /*@
    loop invariant 0 <= low;
    loop invariant high < length;
    loop invariant \forall integer i; 0 <= i < low ==> arr[i] < query;
    loop invariant \forall integer i; high < i < length ==> arr[i] > query;
    loop variant high - low;
  */
  while (low <= high) {
    int mean = low + (high -low) / 2;
    if (arr[mean] == query) return mean;
    if (arr[mean] < query) low = mean + 1;
    else high = mean - 1;
  }
  return -1;
}

/*
Local Variables:
compile-command: "frama-c -jessie find_array.c"
End:
*/
