union u {
    int a;
    char c;
};

//@ ensures \result == 0;
int f(union u u)
{
    u.a = 0;
    u.c = '0';
   
    return u.a;
}