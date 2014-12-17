

#pragma SeparationPolicy(none)

//@ assigns *res;
void comp ( const unsigned a[2], const unsigned b[2], char *res);


//@ assigns \nothing;
int f(const unsigned a[2], const unsigned b[2])
{
  unsigned res = 0;
  char tmp;
  comp( a, b, &tmp);
 
 // some code here

  return res;
} 
