
/*

C test file

*/

int x;
/* int t[]; */

int f(int y, int ddd, int z) 
/*@ y=ddd */ 
{
  int u = z;
  return u++;
} 
/*@ result = z */

int main() 
{
  x = 0;
  x = f(1,++x,2);
} 
/*@ x = 2 */

