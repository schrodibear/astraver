// extern int printf(char *format, ...);

void
print_equality(x, y)
  int x, y;
{
  //printf("%d == %d\n", x, y);
}

int
main()
{
  int i, j;

  i = 0;
  /*@ assert i == 0; */
  print_equality(i, 0);
  j = i++; i = j;
  /*@ assert i == 0; */
  print_equality(i, 0);
  i = j = i++;
  /*@ assert i == 0; */
  print_equality(i, 0);
  return 0;
}
