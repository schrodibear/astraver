
// 100% proved by gappa

#pragma JessieFloatModel(strict)
//#pragma JessieFloatInstructionSet(x87)

/* to enforce 387 instructions, use :

 gcc -mfpmath=387 fp-test2.c && ./a.out

*/

int main() {
  double tmp1= 0x1p53;
  double tmp2= 0x1p52;
  double a = tmp1 - 1.0;
  double b = tmp2 + 1.0;
  double c = tmp1 * tmp2;
  double res = a*b - c;
  //@ assert ifIEEE744: res == 0.0; // in IEEE 754 mode
  // @ assert ifIntel387: res == 0x1p52; // indeed tmp2, in intel 80 bits mode
  // @ assert ifIntel387: res > 0.0; // indeed tmp2, in intel 80 bits mode
  printf("a=%a b=%a c=%a res=%a\n",a,b,c,res);
  return 0;
}


/* 
Local Variables:
compile-command: "LC_ALL=C make fp-test2"                            
End:
*/
