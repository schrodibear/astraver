
int i = 0;


/*@ requires i==0 || i==1;
  @ behavior b1:
  @   assumes i==0;
  @   ensures \result==0;
  @ behavior b2:
  @   assumes i==1;
  @   ensures \result==1;
*/
int f(){return i;}

/*@ requires 0<=i<=1;
  @ ensures \result==0;
*/
int main(void) 
{ 
  int tmp=f();
  if (tmp) {return 0;}
  return tmp;}
}
