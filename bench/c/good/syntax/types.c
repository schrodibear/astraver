
/* basic types */

char a;
short c;
int b;
long d;
long long e;
float f;
double g;
long double h;

void i;

/* arrays */

char j[5];
long l[5][6];

/* pointers */

int * m;
short ** n;

/* type specifiers */

extern int o;
const char p;
signed char q;
unsigned int r;
signed s; /* defaults to signed int */

/* misc. (specifiers and pointers) */

unsigned char * * t;
const char** u;

/* structures */

struct T; /* forward declaration */
struct S { int fa; }; 
struct T { char fb; float fc; };
struct { int fd :3; } sa; /* bit field */

/* unions */

/* enums */

/* nightmare examples from K&R, section 5.12 */

int (*kra)[13];
int *krb[13];
int *krc();
int (*krd)();
char (*(*kre())[])();
char (*(*krf[3])())[5];

/* typedefs */

