
/*

C test file

*/

int i;
int j;

void test(int k) 
/*@ */
{ 
  int l = 1;
  i = j + k;
  l *= j;
  j += l + 10 * k +i;
}
/*@ i = j@ + k and j = 3 * j@ + 11 * k */


