
struct S { int a; int b[5]; int c; };

struct S s0;

//@ ensures \true
void f() {
  s0.b[2] = 1;
}


struct U { struct S d; int e; };

struct U u;

//@ ensures \true
void g() {
  u.d.b[2] = 1;
}
