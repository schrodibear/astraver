
/* Annotations in C programs */

/*W logic p : int -> prop */

int f(int x) /*@ x = 0 */ {
  return x+1;
} /*@ result = 1 */


/*W external h : int -> int */

int g();

int g() {
  int s = 0;
  int i = 0;
  /*@ assert s = 0 */;
  while (i < 10) /*@ invariant 0 <= i <= 10 variant 10 - i */ 
  {
    s += i++;
  }
} /*@ result > 0 */

/* recursive function with a variant */

int fact(int n) /*@ n >= 0 variant n */ {
  return n == 0 ? 1 : n * fact(n-1);
}

void h() {
  int i = 1000;
  do i--; /*@ i >= 0 */ while (i > 0);
  { 
    int j = 0;
    /*@ assert j = 0 */;
    for (; j < 10; j++) /*@ invariant i >= 0 */ i += j; 
  }
}

