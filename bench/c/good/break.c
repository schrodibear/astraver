
/* break tests */


/*@ ensures \result == 12 */
int f1()
{
  /*@ invariant \true variant 1 */ while (1) break;
  return 12;
}


/*@ ensures \result == 1 */
int f2() 
{
  int n = 10;
  
  /*@ invariant 0 <= n variant n */ 
  while (n >= 0) { 
    if (n == 0) { n++; break; }
    n--;
  }
  return n;
}
    

/*@ ensures \result == 2 */
int f3() 
{
  int n = 10;
  /*@ invariant 1 <= n variant n */
  while (n >= 0) { 
    if (n == 1) { n++; break; }
    n--;
  }
  return n;
}
    
/*@ ensures \result == 3 */
int f4(int x) 
{ 
  int i = 0;
  /*@ invariant i <= 3 variant 10 - i */
  for (i = 0; i < 10; i++) { 
    if (i == 3) break;
  }
  return i;
}

