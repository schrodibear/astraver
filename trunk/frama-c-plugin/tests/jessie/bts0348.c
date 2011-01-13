/* Frama-C BTS 0348

Status: open

yields:

*/


typedef unsigned int uint32;


uint32 b1(uint32 x, uint32 y)
{
  return x^y;
}


uint32 b2(uint32 x, uint32 y)
{
  return x&y;
}


uint32 b3(uint32 x, uint32 y)
{
  return x|y;
}


uint32 b4(uint32 x)
{
  return ~x;
}




/*
Local Variables:
compile-command: "make bts0348"
End:
*/
