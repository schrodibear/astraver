
int x;
int y;
int z;


/*@ requires \valid(p) 
  @ assigns *p
  @ ensures *p == 0
  @*/
void f(int *p){
  *p=0;
}

//@ requires \valid(p)
void g(int *p){
  *p=0;
}

//@ ensures y == 0
void main (){
  f(&x);
  x=1;
  f(&y);
  g(&z);
}


