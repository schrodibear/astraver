
/*

C test file

*/

int i;
int j;

void test(int k) 
/*@ true */
{ 
  int l = 1;
  int m = 12;
  i = j + k;
  l = l * j ;
  j = j + l + 10 * k + i + m;
}
/*@ true */

/* i == j@ + k and j == 3 * j@ + 11 * k + 12 */


