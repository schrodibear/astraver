struct S { int x; int y;};


//@ ensures \result == 2
int f() {
  struct S a={1,2};
  return a.y;
}


struct U { int z; struct S s; };

//@ ensures \result == 3
int g() {
  struct U u = { 1,{2,3} };
  return u.s.y;
}

