

int x;

/*@ ghost int pre_x = x */

/*@ ensures pre_x == \old(x) */
int f() {
  /*@ set pre_x = x */
  return x++;
}

/******** ghost arrays *******/

/*@ ghost int t[10]*/

int u[5];

/*@ ensures u[0] == \old(u[0]) && t[0] == 3 */
void g (){
  u[1]= 3;
  /*@ set t[0] = u[1]*/
}
