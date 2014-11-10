int x;

/*@ global invariant valid: x < 100; */

/*@ global invariant offset_min : x < 100; */

void f(void) {
    x *= x;
}
