
// 100% proved by gappa

#pragma JessieFloatModel(strict)

int main() {
  double tmp= 0x1p53;
  double x = tmp * (tmp - 2.0);
  //@ assert x == \exact(x);
  double y = tmp - 1.0;
  //@ assert y == \exact(y);
  double res = x - y * y;
  //@ assert res == 0.0;   // OK if IEE-754, but if real mode or FMA: -1.0
  printf("%g\n",res);
}
/* 
Local Variables:
compile-command: "LC_ALL=C make check-fma"                            
End:
*/

