
typedef unsigned long ULONG;
#define N (ULONG)4

ULONG t[N];
void f( )
{
ULONG I;
/*@
invariant 0<=I<=N
variant N-I
*/
for(I=0;I<N;I++)
 t[I]=I;
}
