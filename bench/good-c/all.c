
/* all features, orthogonally */

int x;
int y;

void f1() /*@ */ { x = 0; } /*@ x = 0 */

void f2() /*@ x = 0 */ { x++; } /*@ x = 1 */

void f3() /*@ x = 0 */ { ++x; } /*@ x = 1 */

void f4() /*@ x = 0 */ { y = x++; } /*@ x = 1 and y = 0 */

void f5() /*@ x = 0 */ { y = ++x; } /*@ x = 1 and y = 1 */

void f6() /*@ x = 1 */ { x += 2; } /*@ x = 3 */

void f7a() /*@ x = 0 */ { y = x == 0 ? 1 : 2; } /*@ y = 1 */
void f7b() /*@ x <> 0 */ { y = x == 0 ? 1 : 2; } /*@ y = 2 */

int t[];

void t1() /*@ array_length(t) = 10 and t[0] = 1 */ { y = t[0]; } /*@ y = 1 */

/* BUG CALCUL WP */
/* void t2() */
/* @ array_length(t) = 10 and x = 0 and t[0] = 1 * / { y = t[x++]; } /*@ y = 1 */

/* void t3() */
/* @ array_length(t) = 10 and x = 0 and t[1] = 1 * / { y = t[++x]; } /*@ y = 1 */


/* evaluation order */

void e1() /*@ x = 2 */ { y = x + x++; } /*@ y = 4 */

void e2() /*@ x = 2 */ { y = x + ++x; } /*@ y = 5 */

void e3() /*@ x = 2 */ { y = x++ + x; } /*@ y = 5 */

void e4() /*@ x = 2 */ { y = ++x + x; } /*@ y = 6 */

void e5() /*@ x = 2 */ { y = ++x + x++; } /*@ y = 6 */


