
/* Brute force string matching */

/*W logic match : int array, int, int array, int, int -> prop */

void OUTPUT(int j);

void BF(char x[], int m, char y[], int n) 
/*@ array_length(x) = m and array_length(y) = n and
    0 <= n and 0 <= m */
{
  int i, j;

  for (j = 0; j <= n - m; ++j) 
  /*@ invariant 0 <= j  variant n - m + 1 - j */
  {
    for (i = 0; i < m && x[i] == y[i + j]; ++i) 
    /*@ invariant 0 <= i <= m and match(x,0,y,j,i)  variant m - i */;
    if (i >= m) {
      OUTPUT(j);
      /*@ assert match(x,0,y,j,array_length(x)) */;
    }
  }
}
   

