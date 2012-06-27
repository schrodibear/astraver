#define D 10.0
#define T 1.0

/*@ predicate conflict(real s, real v) =
      \exists real t; 0<=t<=T && s - t * v < D;
*/

/*@ predicate cd1d(real s, real v) = D + T * v > s ; */

/*@ lemma completeness: \forall real s, v; v >= 0.0 ==>
             conflict(s,v) ==> cd1d(s,v); */

#define eps 0x1p-49

#define Dp (D+eps)

/*@ requires 100.>=s>=0. && 1. >=v >= 0.;
       behavior completeness:
          assumes cd1d(s,v);
          ensures \result == 1;
 */
int cd1d_double(double s, double v) {
  return (Dp+T*v>s) ? 1 : 0;
}
