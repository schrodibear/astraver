/* Frama-C BTS 0080

yields:

memory (mem-field(int_M),q_21)
in memory set (mem-field(int_M),p_20),
(mem-field(int_M),q_21)
File "jc/jc_interp_misc.ml", line 707, characters 7-7:
Uncaught exception: File "jc/jc_interp_misc.ml", line 707, characters 7-13: Assertion failed
Jessie subprocess failed: jessie -why-opt -split-user-conj -v -locs tst2.cloc tst2.jc 


Still open

*/


/*@ requires \valid(p) && \valid(q);
    ensures *p == \old(*q);
    ensures *q == \old(*p);
    assigns *p, *q;
*/
void Swap(int *p, int *q)
{
  int temp;
  temp = *p;
  *p = *q;
  *q = temp;
}



/*@ requires \valid(a+ (0..k));
*/
void foo(int a[], int k) {
  Swap(&a[0], &a[k]);
}

/* 
Local Variables:
compile-command: "LC_ALL=C frama-c -jessie bts0080.c"
End:
*/



