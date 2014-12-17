
/* search for a value in an array */

void copy(int t1[], int t2[], int n) 
/*@ array_length(t1) >= n and array_length(t2) >= n */ {
  int i = n;
  while (i-- > 0) 
    /*@ invariant array_length(t2) >= n and i <= n and
                  forall k:int. i <= k < n -> t2[k] = t1[k] 
        variant i */ {
    t2[i] = t1[i];
  }
}
/*@ forall k:int. 0 <= k < n -> t2[k] = t1[k] */

