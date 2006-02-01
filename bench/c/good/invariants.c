
struct s {
  int x;
  int y;
} s;
/*@ invariant i: 0 <= s.x && s.x <= s.y && s.y <= 100 */

const int c[] = {12 , 14 };
/*@ invariant const_c : c[0]==12 */

/*@ requires n>=0 @*/
void f(int n) {
  int t = s.x+n;
  if (t <= s.y - 20) s.x = t + c[0] ;
}

