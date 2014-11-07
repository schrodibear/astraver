
struct innermost {
  int a, b;
  char c;
};

typedef struct innermost innermost;

struct inner {
  innermost innermost1;
  long la, lb;
  innermost innermost2;
};


struct outer {
  struct inner inner1;
  struct inner inner2;
  struct innermost innermost1;
  struct innermost innermost2;
};

struct outer2 {
  struct inner inner1;
  struct inner inner2;
};

//@ assigns \nothing;
int main (void)
{
  struct outer outer1;
  struct inner inner1;
  struct outer2 outer2;


  outer2.inner2.la = 5l;

  outer1.inner1.innermost1.a = 5;
  outer1.inner1.innermost1.c = '5';
  outer1.inner2.innermost1.c = 'a';
  inner1.innermost2.c = '5';
  inner1.innermost1.a = 6;
  //@ assert (struct innermost *)&outer1 == &outer1.inner1.innermost1;
  //@ assert ((struct inner *)&outer1)->innermost1.a == 5;
  //@ assert ((struct innermost *)&outer1)->c == '5';
  //@ assert ((struct innermost *)&outer1)->c == '6';
  return 0;
}
