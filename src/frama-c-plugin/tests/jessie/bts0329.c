/* Frama-C BTS 0329

Status: resolved

*/

/*@ requires \abs(\exact(x)) <= 0x1p-5 
  @     && \round_error(x) <= 0x1p-20;  
  @ ensures \abs(\exact(\result) - \cos(\exact(x))) <= 0x1p-24
  @     && \round_error(\result) <= \round_error(x) + 0x3p-24;  
  @*/
float cosine1a(float x) {
  float r = 1.0f - x * x * 0.5f;
  return r;
}


/*
Local Variables:
compile-command: "LC_ALL=C frama-c -jessie bts0329.c"
End:
*/
