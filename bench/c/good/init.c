
int x = 45;

int t[3] = {1,2,3};
/*@ invariant t_const : t[1] == 2 */

struct S {
  int a;
  int b[3];
};

struct S s = {1,{1,3,4}};
/*@ invariant s_const : s.b[0] == 1 && s.b[2] == 4 */

/*@ ensures \result == 7 */
int f() {
  int y =x;
  return t[1] + s.b[0] + s.b[2];
}



/*@ ensures \result == 4 */
int g() {
  int t[] = {4,5};
  int x = 45;
  return t[0];
}


/*@ ensures \result == 12 */
int h() {
  int u[3] = { 3,4,5 };
  return u[0] + u[1] + u[2];
}
