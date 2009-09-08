#pragma JessieFloatModel(full)

//@ lemma l: \abs(1.5) == 1.5 && \abs(-2) == 2;

//@ logic integer sqr(integer x) = x * x;

//@ logic real sqr(real x) = x * x;
 
//@ lemma l2: sqr(1.5) == 2.25 && sqr(-5) == 25;

//@ predicate is_pos(integer x) = x > 0;

//@ predicate is_pos(real x) = x > 0.0;
 
//@ lemma l3: is_pos(1.5) && ! is_pos(-5);

/*@ requires \is_finite(x) && \is_finite(y) ; // && \is_finite(z);
  @*/
void f(float x, double y) { // long double z){
}

