/* Frama-C BTS 0026

Status: closed

Fixed in Why 2.22
  
*/

#define MAX 5
int c[5] = {0, };
int global = 0;

void main(void)
{
  //@ assert global == 0;
  //@ assert \forall integer i; 0 <= i < MAX ==> c[i] == 0;

}


/* 
Local Variables:
compile-command: "LC_ALL=C frama-c -jessie bts0035.c"
End:
*/



