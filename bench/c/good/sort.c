
/* sort 4 integers */


#if 0
void sort4_1() {
  int a, b, c, d;
  int tmp;
  if (a > b) { tmp = a; a = b; b = tmp; }
  if (c > d) { tmp = c; c = d; d = tmp; }
  if (a > c) { tmp = a; a = c; c = tmp; }
  if (b > d) { tmp = b; b = d; d = tmp; }
  if (b > c) { tmp = b; b = c; c = tmp; }
  /*@ assert a <= b <= c <= d */
}
#endif

#if 0
/*@ requires \valid_range(t,0,4) 
    ensures t[0] <= t[1] <= t[2] <= t[3] */
void sort4_4(int t[]) {
  int tmp;
  if (t[0] > t[1]) { tmp = t[0]; t[0] = t[1]; t[1] = tmp; }
  if (t[2] > t[3]) { tmp = t[2]; t[2] = t[3]; t[3] = tmp; }
  if (t[0] > t[2]) { tmp = t[0]; t[0] = t[2]; t[2] = tmp; }
  if (t[1] > t[3]) { tmp = t[1]; t[1] = t[3]; t[3] = tmp; }
  if (t[1] > t[2]) { tmp = t[1]; t[1] = t[2]; t[2] = tmp; }
}
#endif

/*@ requires \valid(a) && \valid(b) && \valid(c) && \valid(d) &&
  @   a != b && a != c && a != d && b != c && b != d && c != d
  @ ensures *a <= *b <= *c <= *d */
void sort4_2(int *a, int *b, int *c, int *d) {
  int tmp;
  if (*a > *b) { tmp = *a; *a = *b; *b = tmp; }
  if (*c > *d) { tmp = *c; *c = *d; *d = tmp; }
  if (*a > *c) { tmp = *a; *a = *c; *c = tmp; }
  if (*b > *d) { tmp = *b; *b = *d; *d = tmp; }
  if (*b > *c) { tmp = *b; *b = *c; *c = tmp; }
}

#if 0
/*@ requires \valid(a) && \valid(b) && \valid(c) && \valid(d) &&
  @   a != b && a != c && a != d && b != c && b != d && c != d
  @ ensures *a <= *b <= *c <= *d */
void sort4_3(int *a, int *b, int *c, int *d) {
  int tmp;
  //@ assigns *a,*b ensures *a <= *b
  if (*a > *b) { tmp = *a; *a = *b; *b = tmp; }
  //@ assigns *c,*d ensures *c <= *d
  if (*c > *d) { tmp = *c; *c = *d; *d = tmp; }
  //@ assigns *a,*c ensures *a <= *c
  if (*a > *c) { tmp = *a; *a = *c; *c = tmp; }
  //@ assigns *b,*d ensures *b <= *d
  if (*b > *d) { tmp = *b; *b = *d; *d = tmp; }
  //@ assigns *b,*c ensures *b <= *c
  if (*b > *c) { tmp = *b; *b = *c; *c = tmp; }
}
#endif
