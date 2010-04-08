


// naive version

/*@ requires radius > 0.0;
  @ requires radius <= 3.1391; // 3.1393 does not work 
  @ ensures \abs(\result - 3.141592654*2.0*radius) <= 0.01;
  @*/
float Perimeter1(float radius) {
  return 3.14*2.0*radius;
}

// a bit less naive: avoid double <-> float conversion

/*@ requires 0.0 <= radius <= 3.1392; // OK!
  @ ensures \abs(\result - 3.141592654*2.0*radius) <= 0.01;
  @*/
float Perimeter2(float radius) {
  return 6.28f*radius;
}

// more precise value of \pi in logic!

/*@ lemma le_mul: \forall real x,y,z,t;
  @    0.0 <= x <= y && 0.0 <= z <= t ==> x*z <= y*t;
  @*/

/*@ requires 0.0 <= radius <= 3.0; // OK!
  @ ensures \abs(\result - \pi*2.0*radius) <= 0.01;
  @*/
float Perimeter3(float radius) {
  float r = 6.28f*radius;
  //@ assert \abs(r - 6.28*radius) <= 0x1p-19; 
  //@ assert \abs(6.28*radius - \pi*2.0*radius) <= 0x1p-4; 
  return r;
}
