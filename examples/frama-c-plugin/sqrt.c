#pragma JessieFloatModel(strict)


//@ logic real invsqrt(real x) = 1/\sqrt(x);

/*@
 requires 0.5 <= x <= 2;
 ensures \abs(\result - invsqrt(x)) <= 0x1p-6 * \abs(invsqrt(x));
*/
double sqrt_init(double x);


/*@
 requires 0.5 <= x <= 2;
 ensures \abs(\result - \sqrt(x)) <= 0x1p-43 * \abs(\sqrt(x));
*/
double sqrt(double x)
{
  double t, u;
  t = sqrt_init(x);

  u = 0.5 * t * (3 - t * t * x);
  //@ assert \abs(u - 0.5 * t * (3 - t * t * x)) <= 1;
  /*@ assert (0.5 * t * (3 - t * t * x) - invsqrt(x)) / (invsqrt(x)) ==
        - (1.5 + 0.5 * ((t - invsqrt(x)) / (invsqrt(x)))) *
        (((t - invsqrt(x)) / (invsqrt(x))) * ((t - invsqrt(x)) / (invsqrt(x)))); */
  //@ assert \abs(u - invsqrt(x)) <= 0x1p-10 * \abs(invsqrt(x));
  t = u;

  u = 0.5 * t * (3 - t * t * x);
  //@ assert \abs(u - 0.5 * t * (3 - t * t * x)) <= 1;
  /*@ assert (0.5 * t * (3 - t * t * x) - invsqrt(x)) / (invsqrt(x)) ==
        - (1.5 + 0.5 * ((t - invsqrt(x)) / (invsqrt(x)))) *
        (((t - invsqrt(x)) / (invsqrt(x))) * ((t - invsqrt(x)) / (invsqrt(x)))); */
  //@ assert \abs(u - invsqrt(x)) <= 0x1p-10 * \abs(invsqrt(x));
  t = u;

  u = 0.5 * t * (3 - t * t * x);
  //@ assert \abs(u - 0.5 * t * (3 - t * t * x)) <= 1;
  /*@ assert (0.5 * t * (3 - t * t * x) - invsqrt(x)) / (invsqrt(x)) ==
        - (1.5 + 0.5 * ((t - invsqrt(x)) / (invsqrt(x)))) *
        (((t - invsqrt(x)) / (invsqrt(x))) * ((t - invsqrt(x)) / (invsqrt(x)))); */
  //@ assert \abs(u - invsqrt(x)) <= 0x1p-10 * \abs(invsqrt(x));
  t = u;

  //@ assert x * (invsqrt(x)) == \sqrt(x);
  return x * t;
}
