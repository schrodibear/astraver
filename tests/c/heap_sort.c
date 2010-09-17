
#include "binary_heap.h"


/*@ requires len >= 0;
  @ requires \valid_range(arr,0,len-1);
  @ // assigns arr[..];
  @ ensures \forall integer i,j; 0 <= i <= j < len ==> arr[i] <= arr[j]; 
  @*/
void heap_sort(int *arr, uint len) {
  uint i;
  heap h = create(len);
  /*@ loop invariant 0 <= i <= len;
    @ loop variant len - i;
    @*/
  for (i = 0; i < len; ++i) insert(h,arr[i]);
  /*@ loop invariant 0 <= i <= len;
    @ loop variant len - i;
    @*/
  for (i = 0; i < len; ++i) arr[i] = extract_min(h);
}



void main() {
  int arr[] = {42, 13, 42};
  heap_sort(arr,3);
  //@ assert arr[0] <= arr[1] && arr[1] <= arr[2];
  //@ assert arr[0] == 13 && arr[1] == 42 && arr[2] == 42;
}
  
