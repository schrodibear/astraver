
/* sort 4 integers */

/*@ ensures *a <= *b <= *c <= *d */
void sort4(int *a, int *b, int *c, int *d) {
  if (*a > *b) { int tmp = *a; *a = *b; *b = tmp; }
  if (*c > *d) { int tmp = *c; *c = *d; *d = tmp; }
  if (*a > *c) { int tmp = *a; *a = *c; *c = tmp; }
  if (*b > *d) { int tmp = *b; *b = *d; *d = tmp; }
  if (*b > *c) { int tmp = *b; *b = *c; *c = tmp; }
}
