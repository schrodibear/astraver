void f(int *x) {
    //@ assert \valid(x+(..));
    //@ assert \valid(x + (1..0));
    // assert \valid{Here}(\empty);
}
