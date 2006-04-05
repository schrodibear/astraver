
/*

C test file

*/

int x;
/* int t[]; */

/*@ requires y == ddd assigns \nothing ensures \result == z */ 
int f(int y, int ddd, int z) 
{
  int u = z;
  return u++;
} 

/*@ ensures x == 2 */
void main() 
{
  x = 0;
  x = f(1,++x,2);
} 

