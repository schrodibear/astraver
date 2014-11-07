
/* Frama-C BTS 0284

Status: open

*/


int x = 3;

int t[] = {4,5};

//@ ensures \result == 8;
int main() {
  return x+t[1];
}


/* 
Local Variables:
compile-command: "LC_ALL=C frama-c -jessie bts0284.c"
End:
*/



