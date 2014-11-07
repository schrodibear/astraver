
int c = 0;

typedef int intuint;

//@ type invariant intuint1 (intuint i) = i >=0 ;

//@ global invariant inv1: c == 0;

int g(int *k);

//@ assigns \nothing;
int f(intuint d)
{
  int a;
  g(&a);
  //@ assert c == 0;
  //@ assert intuint1(d);
  //@ assert d >= 0;
  return 0;
}

