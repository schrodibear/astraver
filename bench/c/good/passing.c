
/*

C test file

*/

int t[];

/*@ ensures *x == 0 */
void g(int* x) { *x = 0; }

int * r;

/*@ ensures \result == 0 */
int g2() { g(r); return *r; }

/*@ ensures \result == 0 */
int g3() { int i = 1; g(&i); return i; }

/*@ requires \length(x) == 1 ensures x[0] == 1 */ 
void f(int x[]) { 
  x[0] = 1;
}

/*@ requires \length(t) == 1 ensures t[0] == 1 */ 
void main() {
  f(t);
} 



  
