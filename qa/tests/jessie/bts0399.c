/* Frama-C BTS 0399

Status: solved

*/


int f(int x)
{ int y=0;
 //@ assigns y; ensures y==3;
 y=x;
 //@ assert y>0;
 return y;
}


void main(int x)
{
int y=0;

//@ requires x>0; assigns y; ensures y==x;
y=x;

//@ assert y>0;
}



/*
Local Variables:
compile-command: "make bts0399"
End:
*/
