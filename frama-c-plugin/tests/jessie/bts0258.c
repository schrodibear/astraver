/* Frama-C BTS 0258

yields:

jessie] failure: Unexpected failure.
                  Please submit bug report (Ref. "interp.ml:589:14").

Still open

*/


typedef struct {int a;} T;
T Sa ;
/*@ ensures Sa == \old(Sa);
*/
void f (void) {
}

/* 
Local Variables:
compile-command: "LC_ALL=C frama-c -jessie bts0258.c"
End:
*/
