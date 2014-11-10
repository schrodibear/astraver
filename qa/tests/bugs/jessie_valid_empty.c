void f(int *x, int n, int k) {
    // assert \valid(x+(..));
    //@ assert \valid(x + (1..0));
    //@ assert \valid(x + (n..k));
    //@ assert \valid(x + (n..5));
    // assert \valid{Here}(\empty);
}
