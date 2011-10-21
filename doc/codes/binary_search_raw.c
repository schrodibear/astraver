#pragma JessieIntegerModel(math)
#pragma JessieTerminationPolicy(user)

int binary_search(long t[], int n, long v) {
  int l = 0, u = n-1;
  while (l <= u) {
    int m = (l + u) / 2;
    if (t[m] < v)
      l = m + 1;
    else if (t[m] > v)
      u = m - 1;
    else return m; 
  }
  return -1;
}
