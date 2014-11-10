int x;

/*@ global invariant valid: x < 100; */

void f(void) {
    x *= x;
}
