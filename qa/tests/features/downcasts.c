
int acc(int *a)
{
  return *a;
}

int acc2(void *b)
{
  return acc((int*)b);
}

int g;

/*@ assigns \nothing;
  @ ensures \result == 0;*/
int main()
{
  char *b = 0;
  g = 0;
  return acc2(&b) & g;
}
