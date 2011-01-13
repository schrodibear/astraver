/* Frama-C BTS 0303

Status: Duplicate of 0039

yields:

File "why/bts0303.why", line 819, characters 123-138:
Application to int_P_int_M_a_5 creates an alias

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


void Foo() {
  const int n=10;
  int a[n];
  int i;

  for(i=0; i<n; i++) a[i]=0;
  //@ loop assigns a[0..n-1];
  for(i=1; i<n; i++) Swap(&a[i], &a[0]);
}


/*
Local Variables:
compile-command: "make bts0303"
End:
*/
