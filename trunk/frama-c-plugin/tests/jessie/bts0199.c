/* Frama-C BTS 0199

Status: closed

Note: it is incorrect C code anyway: "a" instead of 'a'

*/

# pragma JessieIntegerModel(math)

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
