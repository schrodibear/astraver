#define ZERO 0
int gFlag =0;

/*@ requires x>0; 
  @ ensures \result >= x && \result >= y && \result>ZERO; 
  @ ensures \result == x || \result == y; 
@*/ 
int max (int x, int y) 
{ 
  int zz=1;
  if (x>y) return x;
  /*@ assert zz>0; @*/ 
  return y;

} 

int main(void){
  return max(0,1);
}
