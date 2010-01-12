/* run.config
   DONTRUN: oracle missing in svn
*/
/* Frama-C BTS 0329

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
compile-command: "LC_ALL=C frama-c -jessie bts0329.c"
End:
*/
