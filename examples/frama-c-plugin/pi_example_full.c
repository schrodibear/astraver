#pragma JessieFloatModel(full)

/*@ lemma le_mul: \forall real x,y,z,t;
  @    0.0 <= x <= y && 0.0 <= z <= t ==> x*z <= y*t;
  @*/


/*@
requires \is_finite(radius) && radius > 0.0 && radius <= 3.0;
ensures \is_finite(\result) && \abs(\result - 3.141592654*2.0*radius) <= 0.01;
*/
float Perimeter(float radius) {
  float a = 6.28f;
  //@ assert \is_finite(a);
  //@ assert 6.27 <= a <= 6.29;
  float r = a*radius;
  //@ assert 0.0 <= a*radius <= 6.29 * 3.0;
  //@ assert \is_finite(r);
  return r;
}
