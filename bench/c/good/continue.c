
/* continue tests */

/*@ ensures \result == 0 */
int f1()
{
  int n = 10;
  /*@ invariant 0 <= n variant n */ 
  while (n > 0) {
    if (n == 5) { n = 0; continue; }
    n--;
  }
  return n;
}

/*@ ensures \result == 10 */
int f2()
{
  int i = 17;
  /*@ invariant i <= 10 variant 10 - i */ 
  for (i = 0; i < 10; i++) {
    if (i == 5) { i = 6; continue; }
  }
  return i;
}

  
