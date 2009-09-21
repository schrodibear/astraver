/* run.config
   DONTRUN: bug JC (Why: Unbound variable char_P_char_M_foo_6)
 */
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


/*@ requires strcmp(foo(x),foo(y));*/
int f (int x, int y) { return x + y; }