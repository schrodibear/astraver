// 100% proved by combination of gappa and SMT

#pragma JessieFloatModel(full)

/* #include<stdio.h> */


int main() {
  double v=0x1.0p600;
  //double v=1e+308; problems with decimal constants in SMT provers

  //@ assert v == \exact(v); // by gappa
  //@ assert \is_finite(v); // by Alt-Ergo, CVC3
  //@ assert v == 0x1.0p600; // by Alt-Ergo, CVC3, Gappa
  //@ assert !\no_overflow(\Double,\NearestEven,v*v); // by gappa
  double x= (v*v)/v;
  //@ assert \is_plus_infinity(x); // by CVC3
  // @ assert x==v;
  printf("%a %d\n",x,x==v);
  return 0;
}

/* 
Local Variables:
compile-command: "LC_ALL=C make fp-intel"                           
End:
*/
