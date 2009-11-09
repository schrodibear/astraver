
// the following pragma allows to ignore potential arithmetic overflow
#pragma JessieIntegerModel(exact)



/*@ requires n >= 0;
  @ decreases n; 
  @*/
int even(int n);

/*@ requires n >= 0;
  @ decreases n; 
  @*/
int odd(int n);

int even(int n) {
  if (n == 0) return 1;
  return ! odd(n-1);
}

int odd(int n) {
  if (n == 0) return 0;
  return ! even(n-1);
}

/* 
Local Variables:
compile-command: "LC_ALL=C make decreases"
End:
*/
