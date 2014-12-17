
// uncomment to show insufficient error message wrt union:
#define testUnion



#define NULL		((void*)0)

/*@
    requires s != NULL;
    ensures \result != 0;
*/
int conv(char *s)
{
#ifdef testUnion
    union _u { char *s; int a; } u;
    u.s = s;
    return u.a;
#else
    return (int)s;
#endif
}

