
/*

C test file

*/

int i;
int j;

/*@ ensures i == \old(j) + k && j == 3 * \old(j) + 11 * k + 12 */
void test(int k) 
{ 
  int l = 1;
  int m = 12;
  i = j + k;
  l = l * j ;
  j = j + l + 10 * k + i + m;
}

/* axiom to help simplify make the proof */
/* @ axiom dist1: \forall int x, int y, int z; x*(y+z) = x*y + x*z */
