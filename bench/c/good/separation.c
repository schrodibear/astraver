
struct s {
  int t[2];
  int u[3];
} s;

int v[4];

//@ ensures \result == 1
int f() {
  s.t[0] = 1;
  s.u[0] = 2;
  v[0] = 3;
  return s.t[0];
}

int g(){
  return v[0];
}

/*@ ensures \result == v[0] */
int g0();

struct {
  int x[1];
} tab[5];


int h(){
  return tab[0].x[0];
}

/* Dillon's example */

typedef struct { 
  int p1[5]; 
  int p2[5];
  int v1; 
  int v2;
} las; 

/*@ requires 
  @   \valid(p) && \valid(p->p1) && \valid(p->p2) 
  @   && \valid_range(p->p1,0,5) && \valid_range(p->p2,0,5) 
  @ assigns p->p1[0 .. 5],p->p2[0 .. 5], p->v1, p->v2 
  @ (* ensures ... *)
  @*/ 
void g1(las * p); 

las u1, u2; 

/*@ requires 
  @   (\forall las *x; (x==&u1 || x==&u2) => 
  @      \valid(x) && \valid(x->p1) && \valid(x->p2) 
  @      && \valid_range(x->p1,0,5) && \valid_range(x->p2,0,5)) 
  @ assigns 
  @   u1.v1,u1.v2,u1.p1[0 .. 5],u1.p2[0 .. 5], 
  @   u2.v1,u2.v2,u2.p1[0 .. 5],u2.p2[0 .. 5] 
  @ (* ensures ... *) 
  @*/ 
void f1() { 
  g1(&u1); g1(&u2); 
}

/* Dillon's example of separation hypothesis of large size */
 
typedef struct { 
  int p1[5]; 
  int p2[5]; 
  int v1; 
  int v2; 
  int * p3; 
  int * p4; 
  int * p5; 
  int * p6; 
  int * p7; 
  int * p8; 
  int * p9; 
  int * p10;
} las2; 

/*@ requires 
  @   \valid(p) && \valid(p->p1) && \valid(p->p2) 
  @   && \valid_range(p->p1,0,5) && \valid_range(p->p2,0,5) 
  @ assigns p->p1[0 .. 5],p->p2[0 .. 5], p->v1, p->v2 
  @ (* ensures ... *)
  @*/ 
void g3(las2 * p); 

las2 u3, u4; 


/* ajout : */ 
las2 w1,w2,w3,w4,w5,w6,w7,w8,w9,w10; 
las2 var1,var2,var3,var4,var5,var6,var7,var8,var9,var10; 

/*@ requires 
  @   (\forall las2 *x; 
  @      (x==&u3 || x==&u4 || x==&w1 || x==&w2 || x==&w3 || x==&w4 || x==&w5 
  @      || x==&w6 || x==&w7 || x==&w8 || x==&w9 || x==&w10) => 
  @      \valid(x) && \valid(x->p1) && \valid(x->p2) && \valid_range(x->p1,0,5) 
  @      && \valid_range(x->p2,0,5)) 
  @ assigns u3.v1,u3.v2,u3.p1[0 .. 5],u3.p2[0 .. 5], 
  @   u4.v1,u4.v2,u4.p1[0 .. 5],u4.p2[0 .. 5], 
  @   w1.v1,w1.v2,w1.p1[0 .. 5],w1.p2[0 .. 5], 
  @   w2.v1,w2.v2,w2.p1[0 .. 5],w2.p2[0 .. 5], 
  @   w3.v1,w3.v2,w3.p1[0 .. 5],w3.p2[0 .. 5], 
  @   w4.v1,w4.v2,w4.p1[0 .. 5],w4.p2[0 .. 5], 
  @   w5.v1,w5.v2,w5.p1[0 .. 5],w5.p2[0 .. 5], 
  @   w6.v1,w6.v2,w6.p1[0 .. 5],w6.p2[0 .. 5], 
  @   w7.v1,w7.v2,w7.p1[0 .. 5],w7.p2[0 .. 5], 
  @   w8.v1,w8.v2,w8.p1[0 .. 5],w8.p2[0 .. 5], 
  @   w9.v1,w9.v2,w9.p1[0 .. 5],w9.p2[0 .. 5], 
  @   w10.v1,w10.v2,w10.p1[0 .. 5],w10.p2[0 .. 5] 
  @ (* ensures ... *) 
  @*/ 
void f3() {
  g3(&u3); 
  g3(&u4); 
  g3(&w1);g3(&w2);g3(&w3);g3(&w4);g3(&w5);
  g3(&w6);g3(&w7);g3(&w8);g3(&w9);g3(&w10); 
}
