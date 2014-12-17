struct p {
  int x;
} p;


struct q {
  struct p *w;
} q;

struct s {
  struct q v;
} s;


struct s u [5];

/*@ assigns a->v.w->x;*/
void h(struct s *a);


void i(){
  int i;

/*@ invariant 0<=i<=5;
  @ loop_assigns u[0 .. 5].v.w -> x;
  @*/
  for (i = 0; i < 5; i++ ){
    h(&u[i]);
  }
}

/*
Local Variables: 
compile-command: "make not_assigns"
End: 
*/
