int foo ()  {
    int x = 42;
    int *y = &x;
    int result;
    asm ("sfsdfsdfsdfsfd" : "=&d" (result) : "a" (y), "m" (*y));
    return result;
}
