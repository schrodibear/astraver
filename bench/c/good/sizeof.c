
/*@ ensures \result == 4 */
int f1() { return sizeof(long int); }

/*@ ensures \result == 34 */
int f2() { return sizeof(short[17]); }

typedef struct { int x :16; int y :16; } tau;
/*@ ensures \result == 4 */
int f3() { return sizeof(tau); }

