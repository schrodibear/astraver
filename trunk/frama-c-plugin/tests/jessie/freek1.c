extern int printf(char *format, ...);

void
expected_actually(x, y)
  int x, y;
{
  printf("expected: %d, actually: %d\n", x, y);
}

int i;
int *p;

/*@ assigns p
  @ ensures p == &i && \valid(p) */
void
mk_alias()
{
  p = &i;
}

/*@ requires \valid(q)
  @ assigns *q
  @ ensures \result == \old(*q) && *q == \old(*q) + 1 */
int
inc(q)
  int *q;
{
  return (*q)++;
}

/*@ assigns i, p */
int
main()
{
  int left, right, value;

  mk_alias();

  i = 0;
  left = inc(p);
  right = i;
  value = left + right;
  /*@ assert value == 1 */
  expected_actually(1, value);

  i = 0;
  value = inc(p) + i;
  /*@ assert value == 1 */
  expected_actually(1, value);

  i = 0;
  left = i;
  right = inc(p);
  value = left + right;
  /*@ assert value == 0 */
  expected_actually(0, value);

  i = 0;
  value = i + inc(p);
  /*@ assert value == 0 */
  expected_actually(0, value);

  return 0;
}
