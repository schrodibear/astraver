
/* search for a value in an array */

int index(int t[], int n, int v) /*@ array_length(t) = n */ {
  int i = 0;
  while (i < n) 
    /*@ invariant 0 <= i and forall k:int. 0 <= k < i -> t[k] <> v
        variant n - i */ {
    if (t[i] == v) break;
    i++;
  }
  return i;
}
/*@ 0 <= result < n -> t[result] = v */

/* same thing, with a return instead of a break */

int index2(int t[], int n, int v) /*@ array_length(t) = n */ {
  int i = 0;
  while (i < n) 
    /*@ invariant 0 <= i and forall k:int. 0 <= k < i -> t[k] <> v
        variant n - i */ {
    if (t[i] == v) return i;
    i++;
  }
  return n;
}
/*@ 0 <= result < n -> t[result] = v */
