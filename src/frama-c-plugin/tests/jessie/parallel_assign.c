
double t[10];

void f() {
  t[0] = 1.0;
  t[1] = 2.0;
  //@ assert t[0] == 1.0;
}

//@ requires \valid(t+(0..14));
void g(double t[15]) {
  t[0] = 1.0;
  t[1] = 2.0;
  t[2] = 3.0;
  //@ assert t[0] == 1.0;
}

/* 
Local Variables:
compile-command: "LC_ALL=C make parallel_assign"
End:
*/
