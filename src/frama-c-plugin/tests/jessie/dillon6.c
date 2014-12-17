typedef struct { int a; } las;

//@ requires \valid(p);
void g(int*p);

las v; 

void f(){
  g(&v.a);
} 
