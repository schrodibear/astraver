


struct {
  int x;
  int y;
} s;

const int c[] = {12 , 14 };
/*@ invariant const_c : c[0]==12 */

/*@ invariant valid_s : \valid(s) */
/*@ invariant i: 0 <= s.x && s.x <= s.y && s.y <= 100 */

/*@  requires n>=0 
  @*/
void f(int n,int a[]) {
  int t = s.x+n;
  a[0] = 0;
  if (t <= s.y - 20) s.x = t + c[0] ;
}

void main() {
  f(0,c);
}

