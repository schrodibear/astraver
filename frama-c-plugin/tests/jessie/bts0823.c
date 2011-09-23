#pragma SeparationPolicy(none)
//#include <stdio.h>

/*@ requires \valid(x);
    requires \valid(y);
    ensures *x == \old(*x);
*/
void ftest(int *x, unsigned int *y)
{
    *y = 123;
}

int p = 0;
unsigned int * const q = &p;

/*@ requires \valid(&p);
    requires \valid(q);
    ensures  p == \old(p);
*/
int main(void)
{
//  printf("old p=%d\n",p);
    ftest(&p,q);
//  printf("new p=%d\n",p);
    return 0;
}

