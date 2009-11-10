
/* McCarthy's ``91'' function. */

#pragma JessieIntegerModel(math)

/*@ behavior less_than_101:
  @   assumes n <= 100;
  @   ensures \result == 91;
  @ behavior greater_than_100:
  @   assumes n >= 101;
  @   ensures \result == n - 10;
  @ decreases 101-n ;
  @*/
int f91(int n) {
  if (n <= 100) {
    return f91(f91(n + 11));
  }
  else
    return n - 10;
}


/* non-recursive version */

/*@ axiomatic F91 {
  @  logic integer f(integer x);
  @  axiom f_def1 : \forall integer x; x >= 101 ==> f(x) == x-10;
  @  axiom f_def2 : \forall integer x; x <= 101 ==> f(x) == 91;
  @
  @  logic integer iter_f(integer n, integer x); // iter_f(n,x) = f^n(x) 
  @  axiom iter_f_def1 : \forall integer x; iter_f(0, x) == x;
  @  axiom iter_f_def2 : 
  @    \forall integer n,x; n > 0 ==> iter_f(n, x) == iter_f(n-1,f(x));
  @ }
  @*/

// for termination
/*@ axiomatic Pair {
  @   type pair_type;
  @   logic pair_type pair(integer x, integer y);
  @ }
  @*/

/*@ inductive lex(pair_type p1, pair_type p2) {
  @  case lex1: \forall integer x1,y1,x2,y2; 
  @      0 <= x2 && x1 < x2 ==> lex(pair(x1,y1),pair(x2,y2)) ;
  @  case lex2: \forall integer x,y1,y2; 
  @      0 <= y2 && y1 < y2 ==> lex(pair(x,y1),pair(x,y2)) ;
  @ }
  @*/

/*@ requires n >= 1;
  @ ensures \result == iter_f(n,x);
  @*/
int f91_nonrec(int n, int x) {
  /*@ loop invariant n >= 0; 
    @ loop invariant iter_f(n,x) == \at(iter_f(n,x),Pre); 
    @ // loop variant pair(101-x+10*n,n) for lex;
    @*/
  while (n > 0) {
    if (x > 100) { x -= 10; n--; }
    else { x += 11; n++; }
  }
  return x;
}


