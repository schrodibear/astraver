

typedef struct{int * p2;} las;

int f3(  las*  p1,  int*  p2); 

/*@ requires \valid(p1)
  @ ensures \result == 0 
  @*/ 
int f3(  las*  p1,  int*  p2) 
{ 
  p1->p2 = p2; 
  return ( 0 ); 
}




typedef struct st {  int p;} st; 
/* ... */ 
void f4(  int*  p); 
/* ... */ 
void f4(  int*  p){}

/*@ requires \valid(p)*/ 
void f4(  int*  p); 
