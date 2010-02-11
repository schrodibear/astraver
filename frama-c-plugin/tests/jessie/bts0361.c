
void ftest(void)
{
    int j = 3;
    int b[10];
M:

    b[j++] = 3;
    // "why" reports "Unbound label 'M'"
    //@ assert j == \at(j,M) + 1;
}

