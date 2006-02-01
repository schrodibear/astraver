struct S{ int x[1]; int y [2];}s;

/*@ ensures s.x[0] == 1*/
void f (){
  s.x[0] = 1;
  s.y[1] = 2;
}


typedef struct T {
  struct S *p;
} T;

T *t,*u;


int g() {
  return t->p->x[0] + u->p->x[0];
}
