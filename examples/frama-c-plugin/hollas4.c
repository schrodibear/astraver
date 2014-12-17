/*@ requires 0 <= a <= 11;
    ensures 0 <= \result <= 10;
 */
int foo(int a);


/*@ requires 0 <= a <= 10;
    ensures 0 <= \result <= 11;
 */
int foo(int a) {
  if(a==11) return 1/(a-11);
  return a;
}

