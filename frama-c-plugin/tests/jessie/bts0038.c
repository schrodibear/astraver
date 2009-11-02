/* Frama-C BTS 0038

Status: open

yields:


File "why/bts0038.why", line 644, characters 10-45:
Term i is expected to have type int

*/

void Copy(int *p, int *q)
{
  *q = *p;
}


int foo(int a[]) {
  int i=1;

  Copy(&a[0], &a[i]);
  return i;
}


int main() {
  int a[2] = {1,2};
  printf("%d\n", foo(a));
}


/* 
Local Variables:
compile-command: "LC_ALL=C frama-c -jessie bts0038.c"
End:
*/
