

/* contribution by Guillaume Melquiond */

// RUN GAPPA (does not work)

#pragma JessieFloatModel(strict)

/*@
 requires 0.5 <= x <= 2;
 ensures \abs(\result - 1/\sqrt(x)) <= 0x1p-6 * \abs(1/\sqrt(x));
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
  /*@ assert (0.5 * t * (3 - t * t * x) - 1/\sqrt(x)) / (1/\sqrt(x)) ==
        - (1.5 + 0.5 * ((t - 1/\sqrt(x)) / (1/\sqrt(x)))) *
        (((t - 1/\sqrt(x)) / (1/\sqrt(x))) * ((t - 1/\sqrt(x)) / (1/\sqrt(x)))); */
  //@ assert \abs(u - 1/\sqrt(x)) <= 0x1p-10 * \abs(1/\sqrt(x));
  t = u;

  u = 0.5 * t * (3 - t * t * x);
  //@ assert \abs(u - 0.5 * t * (3 - t * t * x)) <= 1;
  /*@ assert (0.5 * t * (3 - t * t * x) - 1/\sqrt(x)) / (1/\sqrt(x)) ==
        - (1.5 + 0.5 * ((t - 1/\sqrt(x)) / (1/\sqrt(x)))) *
        (((t - 1/\sqrt(x)) / (1/\sqrt(x))) * ((t - 1/\sqrt(x)) / (1/\sqrt(x)))); */
  //@ assert \abs(u - 1/\sqrt(x)) <= 0x1p-10 * \abs(1/\sqrt(x));
  t = u;

  u = 0.5 * t * (3 - t * t * x);
  //@ assert \abs(u - 0.5 * t * (3 - t * t * x)) <= 1;
  /*@ assert (0.5 * t * (3 - t * t * x) - 1/\sqrt(x)) / (1/\sqrt(x)) ==
        - (1.5 + 0.5 * ((t - 1/\sqrt(x)) / (1/\sqrt(x)))) *
        (((t - 1/\sqrt(x)) / (1/\sqrt(x))) * ((t - 1/\sqrt(x)) / (1/\sqrt(x)))); */
  //@ assert \abs(u - 1/\sqrt(x)) <= 0x1p-10 * \abs(1/\sqrt(x));
  t = u;

  //@ assert x * (1/\sqrt(x)) == \sqrt(x);
  return x * t;
}
