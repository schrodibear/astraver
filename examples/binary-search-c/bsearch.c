
/*W logic In : int array,int,int,int -> prop */

int binary_search(int t[], int n, int v) 
/*@ array_length(t) = n and n >= 0 and sorted_array(t,0,n-1) */
{
  int l,u,p,m;
  l = 0; 
  u = n-1; 
  p = -1;
  while (l <= u) 
    /*@ invariant 
	  0 <= l and u <= array_length(t)-1 and -1 <= p <= array_length(t)-1
          and (p = -1 -> In(t,0,array_length(t)-1,v) -> In(t,l,u,v))
          and (p >= 0 -> t[p]=v)
        variant 2+u-l */ {
    m = (l + u) / 2;
    /*@ assert l <= m and m <= u */;
    if (t[m] < v)
      l = m + 1;
    else if (t[m] > v)
      u = m - 1;
    else
      return m;
  }
  return -1;
}
/*@ (0 <= result <= array_length(t)-1 and t[result]=v) or 
    (result = -1 and not In(t,1,array_length(t)-1,v)) */


