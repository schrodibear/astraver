
float v;

typedef struct {float f0;float f1;float f2;} ts;
typedef ts las;

/*@ axiomatic MyCast {
  @  predicate simulated_cast{L}(las *p, float*t);
  @  axiom a{L} : \forall las *p; \forall float * t;
  @    simulated_cast(p,t) ==> p->f0==t[0] && p->f1==t[1] && p->f2==t[2];
  @  axiom b{L} : \forall las * p; \forall float * t;
  @    simulated_cast(p,t) && \valid(p) ==> \valid(t+(0..2));
  @ }
  @*/
 
/*@ assigns \nothing;
  @ ensures simulated_cast(x,\result);
  @*/
float *simulated_cast_to_float_ptr(las *x);

/*@ requires \valid(d+(0..2));
  @ assigns v;
  @ ensures v == d[1];
  @*/
void f(float d[])
{ v = d[1]; }

//@ ensures v==9.0;
void main()
{
  las x;
  x.f1 = 9.0;
  f(simulated_cast_to_float_ptr(&x)); 
} 
