
/* Brute force string matching */

/*W logic match : int array, int, int array, int, int -> prop */

void OUTPUT(char x[], char y[], int j) 
     /*@ pre match(x,0,y,j,array_length(x)) reads x,y */;

void BF(char x[], int m, char y[], int n) 
/*@ 0 <= n and 0 <= m and array_length(x) = m and array_length(y) = n */
{
  int i = 0, j = 0;

  for (j = 0; j <= n - m; ++j) 
  /*@ invariant 0 <= j <= n - m + 1  variant n - m + 1 - j */
  {
    for (i = 0; i < m && x[i] == y[i + j]; ++i) 
    /*@ invariant 0 <= i <= m and match(x,0,y,j,i)  variant m - i */;
    if (i >= m)
      OUTPUT(x,y,j);
  }
}
   

