
/* continue tests */

int f1()
{
  int n = 10;
  while (n > 0) 
    /*@ invariant 0 <= n variant n */ {
    if (n == 5) { n = 0; continue; }
    n--;
  }
  return n;
}
/*@ result = 0 */


int f2()
{
  int i = 17;
  for (i = 0; i < 10; i++)
    /*@ invariant i <= 10 variant 10 - i */ {
    if (i == 5) { i = 6; continue; }
  }
  return i;
}
/*@ result = 10 */

  
