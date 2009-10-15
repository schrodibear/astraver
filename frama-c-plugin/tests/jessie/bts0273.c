/* Frama-C BTS 0273 

yields:

Uncaught exception: File "jc/jc_interp.ml", line 1819, characters 1-7: Assertion failed

Fixed in Why 2.21

*/

typedef float real;
struct T26_27 { real _F0 ; real _F1 ; };
typedef struct T26_27 _T26;
struct T28_29 { _T26 _F0 ; _T26 _F1 ; };
typedef struct T28_29 _T28;
typedef _T28 RR;
void f(RR const *tab , real *y )
{ *y = (float )(double )(*((real *)tab + 1)); }


/* 
Local Variables:
compile-command: "LC_ALL=C frama-c -jessie bts0273.c"
End:
*/
