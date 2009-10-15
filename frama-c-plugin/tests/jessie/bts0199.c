/* Frama-C BTS 0199

yields:

error: unexpected error File "src/jessie/interp.ml", line 1764,
characters 18-24: Assertion failed


Still open

*/

float v;

static void fun(void)
{
  switch ("a")
    {
    case "a":
      if (v > fabs(1))
        {
        }
      break;
    }
}


/*
Local Variables:
compile-command: "LC_ALL=C frama-c -jessie bts0199.c"
End:
*/
