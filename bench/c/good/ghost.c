

int x;

/*@ ghost int pre_x = x */

/*@ ensures pre_x == \old(x) */
int f() {
  /*@ set pre_x = x */
  return x++;
}
