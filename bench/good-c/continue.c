
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
