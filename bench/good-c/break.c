
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
    

