
/* Not so naive algorithm */

/*W logic match : int array, int, int array, int, int -> prop */

void OUTPUT(int j);

/* NOTE: memcmp changed to avoid pointer arithmetic */
int memcmp(char x[], int i, char y[], int j, int n) 
     /*@ reads x,y
         post (result = 0 -> match(x,i,y,j,n)) 
          and (result <> 0 -> not match(x,i,y,j,n)) */;

void NSN(char x[], int m, char y[], int n) 
/*@ array_length(x) = m and array_length(y) = n and 0 <= n and 2 <= m */
{
   int j, k, ell;
  
   /* Preprocessing */
   if (x[0] == x[1]) {
      k = 2;
      ell = 1;
   }
   else {
      k = 1;
      ell = 2;
   }
   /*@ assert k > 0 and ell > 0 */;
  
   /* Searching */
   j = 0;
   while (j <= n - m)
      /*@ invariant 0 <= j  variant n-m-j */
      if (x[1] != y[j + 1])
         j += k;
      else {
       if (memcmp(x, 2, y, j + 2, m - 2) == 0 &&
             x[0] == y[j]) {
            OUTPUT(j);
	    /*@ assert match(x,0,y,j,array_length(x)) */;
	 }
         j += ell;
      }
}


