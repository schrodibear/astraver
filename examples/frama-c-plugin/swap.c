/*@
  requires \valid(x);
  requires \valid(y);
  assigns *x;
  assigns *y;
  ensures (\at(*x, Post)== \at(*y,Pre)) && (\at(*y, Post) == \at(*x,Pre)) ;
*/

void swap(int* x, int *y){
  int temp;
  temp = *x;
  *x = *y;
  *y = temp;  
}
