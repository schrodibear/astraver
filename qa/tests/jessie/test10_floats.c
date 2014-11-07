
/*@
  requires 3.2 <= x <= 3.3 && 1.4 <= y <= 1.8;
  ensures \result == x - y;
*/
float diff(float x, float y)
{
	return x - y;
}
