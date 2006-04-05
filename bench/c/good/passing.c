
/*

C test file

*/

/*@ requires \valid(x) assigns *x ensures *x == 0 */
void g(int* x) { *x = 0; }

int * r;

/*@ requires \valid(r) ensures \result == 0 */
int g2() { g(r); return *r; }

#if 0
/*@ ensures \result == 0 */
int g3() { int i = 1; g(&i); return i; }
#endif

/*@ requires \valid_index(x,0)  assigns x[0]  ensures x[0] == 1 */ 
void f(int x[]) { 
  x[0] = 1;
}

int t[2];

/*@ ensures t[0] == 1 */ 
void main() {
  f(t);
} 



  
