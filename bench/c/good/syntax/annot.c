
/* Annotations in C programs */

/*W logic p : int -> prop */

/*@ requires x == 0 ensures \result == 1 */
int f(int x) {
  return x+1;
}


/*W external h : int -> int */

int g();

/*@ ensures result > 0 */
int g() {
  int s = 0;
  int i = 0;
  /*@ assert s == 0 */;
  while (i < 10) /*@ invariant 0 <= i <= 10 variant 10 - i */ 
  {
    s += i++;
  }
}

/* recursive function with a variant */

/*@ ensures n >= 0 (* variant n *) */
int fact(int n) {
  return n == 0 ? 1 : n * fact(n-1);
}

void h() {
  int i = 1000;
  do i--; /*@ invariant i >= 0 variant i */ while (i > 0);
  { 
    int j = 0;
    /*@ assert j == 0 */;
    for (; j < 10; j++) /*@ invariant i >= 0 variant i */ i += j; 
  }
}

