typedef union _Integer { int x; char c; } Integer;

//@ ensures 0 <= \result <= 1;
int endianness() {
  Integer i;
  i.x = 1;
  //@ assert i.x == 1;
  //@ assert i.c != 2;
  return i.c;
}

typedef struct _Decomp { char c1; char c2; char c3; } Decomp;
typedef union _Integer2 { int x; Decomp c; } Integer2;

//@ ensures 0 <= \result <= 1;
int endianness2() {
  Integer2 i;
  i.x = 1;
  //@ assert i.x == 1;
  //@ assert i.c.c1 != 2;
  return i.c.c1;
}

typedef union _Integer3 { int x; char c[4]; } Integer3;

//@ ensures 0 <= \result <= 1;
int endianness3() {
  Integer3 i;
  i.x = 1;
  //@ assert i.x == 1;
  //@ assert i.c[0] != 2;
  return i.c[0] == 1;
}

/* 
Local Variables:
compile-command: "LC_ALL=C make -j endian"
End:
*/
