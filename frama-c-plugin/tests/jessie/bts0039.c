/* Frama-C BTS 0040

Status: open

yields:

** Jc_interp_misc.transpose_location_list: TODO: parameters **
memory (mem-field(int_M),b_2)
in memory set (mem-field(int_M),a_1),
(mem-field(int_M),b_2)
File "jc/jc_interp_misc.ml", line 737, characters 1-1:
Uncaught exception: File "jc/jc_interp_misc.ml", line 737, characters 1-7: Assertion failed

Update: now yields

File "why/bts0039.why", line 711, characters 125-140:
Application to int_P_int_M_p_3 creates an alias

See also bts0080.c

*/

typedef struct {int i;int j;} las;

/*@ requires \valid(a) && \valid(b);
   assigns *a, *b; */
void g (int *a,int *b){ *a=11; *b=15; }

/*@ requires \valid(p) ;
assigns p->i,p->j;
*/
void f (las *p)
{ g (&(p->i), &(p->j)); }


/* 
Local Variables:
compile-command: "LC_ALL=C frama-c -jessie bts0039.c"
End:
*/


