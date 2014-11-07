int test(void)
{
    return 0;
}

typeof(test) (*pf (int));

typeof(pf) pf;

extern typeof(test) test;

typeof(&test) ptest;

int a;

typeof(a) b = 1;
typeof(int) c = 0;

typeof(&a) pa = &a;

struct s {
    int f;
} g;
typeof(g) e = {1};

typeof(&g) pe = &e;
typeof(*pe) d = {2};

int arr[5];
typeof(arr) bb = {1, 2, 3, 4, 5};
typeof(&arr) bcc[2] = {&bb, &bb};
typeof(arr[1]) bbb = 1;
typeof(&arr[1]) bbbb = &arr[2];