

/* all features, orthogonally */

int x;
int y;

/*@ ensures x == 0 */
void f1() { x = 0; }

/*@ requires x == 0 
    ensures x == 1 */ 
void f2() { x++; }

/*@ requires x == 0 
    ensures x == 1 */ 
void f3() { ++x; }

/*@ requires x == 0 
    ensures x == 1 && y == 0 */ 
void f4() { y = x++; }

/*@ requires x == 0 
    ensures x == 1 && y == 1 */ 
void f5() { y = ++x; }

/*@ requires x == 1 
    ensures x == 3 */ 
void f6() { x += 2; }

/*@ requires x == 0 
    ensures y == 1 */ 
void f7a() { y = x == 0 ? 1 : 2; }

/*@ requires x != 0 
    ensures y == 2 */ 
void f7b() { y = x == 0 ? 1 : 2; }

int t[];

/*@ requires \valid_index(t,0) && t[0] == 1 
    ensures y == 1 */ 
void t1() { y = t[0]; }

/*@ requires \valid_index(t,0) == 10 && x == 0 && t[0] == 1 
    ensures y == 1 */ 
void t2() { y = t[x++]; }

/*@ requires \valid_index(t,1) == 10 && x == 0 && t[1] == 1 
    ensures y == 1 */ 
void t3() { y = t[++x]; }

/*@ requires \valid_index(t,2) && x == 2 && t[2] == 3 
    ensures x == 3 && t[2] == 5 */ 
void t4() { t[x] += x++; } 

/* evaluation order */

/*@ requires x == 2 
    ensures y == 4 */ 
void e1() { y = x + x++; }

/*@ requires x == 2 
    ensures y == 5 */ 
void e2() { y = x + ++x; }

/*@ requires x == 2 
    ensures y == 5 */ 
void e3() { y = x++ + x; }

/*@ requires x == 2 
    ensures y == 6 */ 
void e4() { y = ++x + x; }

/*@ requires x == 2 
    ensures y == 6 */ 
void e5() { y = ++x + x++; }



