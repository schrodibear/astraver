/* Frama-C BTS 0332

Status: open

*/



/*@ requires \valid(p);
  @ assigns *p;
  @ ensures *p ==  ((e || (t && f)) && (t || f)) ;
  @*/
void f(int*p,int e,int t,int f,int r)
{
  *p = ( (e || (t && f)) && (t || f) );
}



/*
Local Variables:
compile-command: "LC_ALL=C frama-c -jessie -jessie-adhoc-normalization bts0332.c"
End:
*/
