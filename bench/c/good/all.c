
/* all features, orthogonally */

int x;
int y;

/*@ ensures x == 0 */
void f1() { x = 0; }

/*@ requires x == 0 ensures x == 1 */ 
void f2() { x++; }

/*@ requires x == 0 ensures x == 1 */ 
void f3() { ++x; }

/*@ requires x == 0 ensures */ 
void f4() { y = x++; } /*@ x = 1 and y = 0 */

/*@ requires x == 0 ensures x = 1 and y = 1 */ 
void f5() { y = ++x; }

/*@ requires x == 1 ensures x = 3 */ 
void f6() { x += 2; }

/*@ requires x == 0 ensures y = 1 */ 
void f7a() { y = x == 0 ? 1 : 2; }
/*@ requires x != 0 ensures y = 2 */ 
void f7b() { y = x == 0 ? 1 : 2; }

int t[];

/*@ requires \length(t) == 10 && t[0] = 1 */ 
void t1() { y = t[0]; } /*@ y = 1 */

void t2()
/*@ \length(t) = 10 && x = 0 && t[0] = 1 */ { y = t[x++]; } /*@ y = 1 */

void t3()
/*@ \length(t) = 10 && x = 0 && t[1] = 1 */ { y = t[++x]; } /*@ y = 1 */

void t4() 
/*@ \length(t) = 10 && x = 2 && t[2] = 3 */ 
{ t[x] += x++; } 
/*@ x = 3 && t[2] = 5 */

/* evaluation order */

void e1() /*@ x = 2 */ { y = x + x++; } /*@ y = 4 */

void e2() /*@ x = 2 */ { y = x + ++x; } /*@ y = 5 */

void e3() /*@ x = 2 */ { y = x++ + x; } /*@ y = 5 */

void e4() /*@ x = 2 */ { y = ++x + x; } /*@ y = 6 */

void e5() /*@ x = 2 */ { y = ++x + x++; } /*@ y = 6 */


