
struct S {
  int i;
  int j;
};

struct S gv;

void f() {
  struct S lv;
  gv.i = 0;
  gv.j = gv.i + 1;
  lv.i = 0;
  lv.j = lv.i + 1;
  /*@ assert gv.i == lv.i; */
  /*@ assert gv.j == lv.j; */
}

struct T {
  struct S s;
  struct S* sp;
  struct T* tp;
  struct S** spp;
  struct T** tpp;
};

struct T gvt;

/*@ requires \valid(gvt.sp) && \valid(gvt.tp); 
  @ requires \valid(gvt.spp) && \valid(*gvt.spp);
  @ requires \valid(gvt.tpp) && \valid(*gvt.tpp);
  @ */
void g() {
  struct T lvt;
  struct S lvs;
  gvt.s.i = 0;
  gvt.s.j = gvt.s.i + 1;
  gvt.s.i = 0;
  gvt.s.j = gvt.s.i + 1;
  /*@ assert gvt.s.i == lvt.s.i; */
  /*@ assert gvt.s.j == lvt.s.j; */
  lvt.sp = &lvs;
  gvt.sp->i = 0;
  gvt.sp->j = gvt.sp->i + 1;
  lvt.sp->i = 0;
  lvt.sp->j = lvt.sp->i + 1;
  /*@ assert gvt.sp->i == lvt.sp->i; */
  /*@ assert gvt.sp->j == lvt.sp->j; */
  lvt.tp = &lvt;
  gvt.tp->s.i = 0;
  gvt.tp->s.j = gvt.tp->s.i + 1;
  gvt.tp->s.i = 0;
  gvt.tp->s.j = gvt.tp->s.i + 1;
  /*@ assert gvt.tp->s.i == lvt.tp->s.i; */
  /*@ assert gvt.tp->s.j == lvt.tp->s.j; */
  lvt.spp = &lvt.sp;
  (*gvt.spp)->i = 0;
  (*gvt.spp)->j = (*gvt.spp)->i + 1;
  (*lvt.spp)->i = 0;
  (*lvt.spp)->j = (*lvt.spp)->i + 1;
  /*@ assert (*gvt.spp)->i == (*lvt.spp)->i; */
  /*@ assert (*gvt.spp)->j == (*lvt.spp)->j; */
  lvt.tpp = &lvt.tp;
  (*gvt.tpp)->s.i = 0;
  (*gvt.tpp)->s.j = (*gvt.tpp)->s.i + 1;
  (*lvt.tpp)->s.i = 0;
  (*lvt.tpp)->s.j = (*lvt.tpp)->s.i + 1;
  /*@ assert (*gvt.tpp)->s.i == (*lvt.tpp)->s.i; */
  /*@ assert (*gvt.tpp)->s.j == (*lvt.tpp)->s.j; */  
}

/* 
Local Variables:
compile-command: "LC_ALL=C make struct_type"
End:
*/
