//@ predicate is_bit(integer n) = ((n==0)||(n==1));
//@ ensures is_bit(\result);
extern unsigned int nd();

int main(int n)
{
  int b, y;
  int i;
  int x = 10;
  while (i<n)
    {
      b = nd();
      if (b)
	y = x / i;
    }
  //@ assert (x == 10);
  return 0;
}
