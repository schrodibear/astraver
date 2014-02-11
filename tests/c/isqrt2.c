/* run.config
   OPT: -journal-disable -cvcg
*/

/*@ requires 0 <= x <= 32768 * 32768 - 1;
  @ assigns \nothing;
  @ ensures \result >= 0 &&
  @         \result * \result <= x &&
  @         x < (\result + 1) * (\result + 1);
  @*/
int isqrt(int x) {
  int count = 0, sum = 1;
  /*@ loop invariant 0 <= count <= 32767 &&
    @                x >= count * count &&
    @                sum == (count+1)*(count+1);
    @ loop assigns count, sum;
    @ loop variant  x - count;
    @*/
  while (sum <= x) sum += 2 * ++count + 1;
  return count;
}

//@ ensures \result == 4;
int test () {
  int r;
  r = 0 + isqrt(17);
  //@ assert r < 4 ==> \false;
  //@ assert r > 4 ==> \false;
  return r;
}

int main () {
  return 0;
}


/*
Local Variables:
compile-command: "make isqrt2.why3ide"
End:
*/


