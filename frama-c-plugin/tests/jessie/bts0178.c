/* Frama-C BTS 0178

yields:


File "why/simple.why", line 552, characters 9-49:
Term i is expected to have type int


still open

*/



void g(int * j, int *k) {
  int tmp= *j;
  *j=*k;
  *k=tmp;
}

void f(int * vector, int size) {
  int i=0;
  if (i<size)
    g (&vector[i],&vector[i+1]);
}


/* 
Local Variables:
compile-command: "LC_ALL=C frama-c -jessie bts0178.c"
End:
*/



