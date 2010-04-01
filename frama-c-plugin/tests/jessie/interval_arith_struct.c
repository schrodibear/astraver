#pragma JessieFloatModel(full)
#pragma JessieFloatRoundingMode(down)


/*@ requires !\is_NaN(x) && !\is_NaN(y);
  @ ensures \le_float(\result,x) && \le_float(\result,y);
  @ ensures \eq_float(\result,x) || \eq_float(\result,y);
  @*/
double min(double x, double y)
{
  return x < y ? x : y;
}


/*@ requires !\is_NaN(x) && !\is_NaN(y);
  @ ensures \le_float(x,\result) && \le_float(y,\result);
  @ ensures \eq_float(\result,x) || \eq_float(\result,y);
  @*/
double max(double x, double y)
{
  return x > y ? x : y;
}


//@ predicate dif_sign(double x, double y) = \sign(x) != \sign(y);
//@ predicate sam_sign(double x, double y) = \sign(x) == \sign(y);

/*@ predicate double_le_real(double x,real y) = 
  @           (\is_finite(x) && x <= y) || \is_minus_infinity(x);
  @*/

/*@ predicate real_le_double(real x,double y) = 
  @           (\is_finite(y) && x <= y) || \is_plus_infinity(y);
  @*/


/*@ requires ! \is_NaN(x) && ! \is_NaN(y) 
  @    && (\is_infinite(x) ==> y != 0.0 && dif_sign(x,y))
  @    && (\is_infinite(y) ==> x != 0.0 && dif_sign(x,y));
  @ assigns \nothing;
  @ ensures double_le_real(\result,x*y);
  @*/
double mul_dn(double x, double y)
{
  return x * y;
}



/*@ requires !\is_NaN(x) && !\is_NaN(y) && sam_sign(x,y) &&
  @          (\is_infinite(x) ==> y != 0.0 && \abs(y) >= 0x2.0p-1074 ) 
  @          &&
  @          (\is_infinite(y) ==> x != 0.0 )
  @          &&
  @          (\is_finite(y) && !\no_overflow_double(\Down,-y) && \sign(y) == \Positive
                              ==> x != 0.0 );
  @ ensures  real_le_double(x * y,\result);
  @*/
double mul_up(double x, double y)
{
  return -(x * -y);
}



typedef struct { double l, u; } interval;
/*@ type invariant is_interval(interval *x) = 
  @       (\is_finite(x->l) || \is_minus_infinity(x->l)) 
  @       &&
  @       (\is_finite(x->u) || \is_plus_infinity(x->u));
  @*/

/*@ predicate in_interval{L}(real a,interval *x) = 
  @           double_le_real(x->l,a) && real_le_double(a,x->u);
  @*/



/*@ ensures 
  @    \forall real a,b; in_interval(a,&x) && in_interval(b,&y) ==>
  @         in_interval(a+b,&\result);    
  @*/
interval add(interval x, interval y)
{
  interval z;
  z.l = x.l + y.l;
  z.u = -(-x.u - y.u);
  return z;
}


/*@ ensures 
  @   \forall real a,b; in_interval(a,&x) && in_interval(b,&y) ==>
  @                     in_interval(a*b,&\result); 
  @*/
interval mul(interval x, interval y)
{
  interval z;
  if (x.l < 0.0)
    if (x.u > 0.0)
      if (y.l < 0.0)
        if (y.u > 0.0) // M * M
          { z.l = min(mul_dn(x.l, y.u), mul_dn(x.u, y.l));
            z.u = max(mul_up(x.l, y.l), mul_up(x.u, y.u)); }
        else           // M * N
          { z.l = mul_dn(x.u, y.l);
            z.u = mul_up(x.l, y.l); }
      else
        if (y.u > 0.0) // M * P
          { z.l = mul_dn(x.l, y.u);
            z.u = mul_up(x.u, y.u); }
        else           // M * Z
          { z.l = 0.0;
            z.u = 0.0; }
    else
      if (y.l < 0.0)
        if (y.u > 0.0) // N * M
          { z.l = mul_dn(x.l, y.u);
            z.u = mul_up(x.l, y.l); }
        else           // N * N
          { z.l = mul_dn(x.u, y.u);
            z.u = mul_up(x.l, y.l); }
      else
        if (y.u > 0.0) // N * P
          { z.l = mul_dn(x.l, y.u);
            z.u = mul_up(x.u, y.l); }
        else           // N * Z
          { z.l = 0.0;
            z.u = 0.0; }
  else
    if (x.u > 0.0)
      if (y.l < 0.0)
        if (y.u > 0.0) // P * M
          { z.l = mul_dn(x.u, y.l);
            z.u = mul_up(x.u, y.u); }
        else           // P * N
          { z.l = mul_dn(x.u, y.l);
            z.u = mul_up(x.l, y.u); }
      else
        if (y.u > 0.0) // P * P
          { z.l = mul_dn(x.l, y.l);
            z.u = mul_up(x.u, y.u); }
        else           // P * Z
          { z.l = 0.0;
            z.u = 0.0; }
    else               // Z * ?
      { z.l = 0.0;
        z.u = 0.0; }

  return z;
}




/* 
Local Variables:
compile-command: "LC_ALL=C make interval_arith_struct"
End:
*/
