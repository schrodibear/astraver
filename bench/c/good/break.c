
/* break tests */


int f1()
{
  while (1) /*@ invariant true variant 1 */ break;
  return 12;
}
/*@ result = 12 */


int f2() 
{
  int n = 10;
  while (n >= 0) 
    /*@ invariant 0 <= n variant n */ { 
    if (n == 0) { n++; break; }
    n--;
  }
  return n;
}
/*@ result = 1 */
    

int f3() 
{
  int n = 10;
  while (n >= 0) 
    /*@ invariant 1 <= n variant n */ { 
    if (n == 1) { n++; break; }
    n--;
  }
  return n;
}
/*@ result = 2 */
    

int f4(int x) 
/*@ */
{ 
  int i = 0;
  for (i = 0; i < 10; i++)
    /*@ invariant i <= 3 variant 10 - i */
    { 
      if (i == 3) break;
    }
  return i;
}
/*@ result = 3 */

