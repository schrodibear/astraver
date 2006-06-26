
/* integer arithmetic overflows (requires --int-overflow) */

int f1(signed char c, int x) {
  unsigned char uc = 1;
  c = uc;
  return c+(int)c;
}
