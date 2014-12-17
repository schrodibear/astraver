
char T;

/*@
  axiomatic foo {
    logic char* foo{L}(integer x) = &T;
  }
*/

/*@ predicate strcmp{L}(char *x, char* y) =
     \forall integer i; (\forall integer j; 0<=j<i ==> *(x+j) !=0) ==>
           *(x+i) == *(y+i);
*/


/*@ ensures strcmp(foo(x),foo(\result)); */
int f(int x) {
  return x++;
} 
