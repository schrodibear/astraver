#pragma JessieFloatModel(full)
#pragma JessieFloatRoundingMode(downward)


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

/*@ predicate in_interval(real a,double l,double u) = 
  @           double_le_real(l,a) && real_le_double(a,u);
  @*/


/*@ requires ! \is_NaN(x) && ! \is_NaN(y) 
  @    && (\is_infinite(x) ==> y != 0.0 && dif_sign(x,y))
  @    && (\is_infinite(y) ==> x != 0.0 && dif_sign(x,y));
  @ assigns \nothing;
  @ ensures double_le_real(\result,x*y);
  @*/
double mul_dn(double x, double y)
{
  double z = x*y;
  /* @ assert \is_finite(x) && \is_finite(y) 
    @     && \no_overflow(\Double,\Down,x*y) ==> double_le_real(z,x*y);
    @*/
  /* @ assert \is_finite(x) && \is_finite(y) 
    @     && ! \no_overflow(\Double,\Down,x*y) && \sign(x) == \sign(y) ==> double_le_real(z,x*y);
    @*/
  /* @ assert \is_finite(x) && \is_finite(y) 
    @     && ! \no_overflow(\Double,\Down,x*y) && \sign(x) != \sign(y)  ==> double_le_real(z,x*y);
    @*/
  /* @ assert \is_infinite(x) || \is_infinite(y) ==> double_le_real(z,x*y);
    @*/
  return z;
}


/*@ requires !\is_NaN(x) && !\is_NaN(y) && sam_sign(x,y) &&
  @          (\is_infinite(x) ==> y != 0.0 && \abs(y) >= 0x1.0p-1074 ) 
  @          &&
  @          (\is_infinite(y) ==> x != 0.0 )
  @          &&
  @          (\is_finite(y) && !\no_overflow(\Double,\Down,-y) && \sign(y) == \Positive
                              ==> x != 0.0 );
  @ ensures  real_le_double(x * y,\result);
  @*/
double mul_up(double x, double y) {
  double a=-y;
  double b=x*a;
  double z=-b;
  /* double z = -(x * -y);*/

  /* @ assert \is_infinite(x) || \is_infinite(y) ==> real_le_double(x * y,z);
    @*/


  /* @ assert \is_finite(x) && \is_infinite(y) ==> real_le_double(x * y,z) ;
    @*/
  /* @ assert \is_infinite(x) && \is_finite(y) &&
    @    \no_overflow(\Double,\Down,-y) ==> real_le_double(x * y,z);
    @*/
  /* @ assert \is_infinite(x) && \is_finite(y) &&
    @    ! \no_overflow(\Double,\Down,-y) ==> real_le_double(x * y,z);
    @*/
  /* @ assert \is_infinite(x) && \is_infinite(y) ==> real_le_double(x * y,z);
    @*/
  

  /* @ assert \is_finite(x) && \is_finite(y) && 
    @     \no_overflow(\Double,\Down,-y) &&
    @     \no_overflow(\Double,\Down,x*a) && 
    @     !\no_overflow(\Double,\Down,-b) ==> real_le_double(x * y,z) ;
    @*/
  /* @ assert \is_finite(x) && \is_finite(y) && 
    @     \no_overflow(\Double,\Down,-y) &&
    @     !\no_overflow(\Double,\Down,x*a) ==> real_le_double(x * y,z) ;
    @*/
  /* @ assert \is_finite(x) && \is_finite(y) && 
    @     !\no_overflow(\Double,\Down,-y) && \sign(y) == \Positive 
    @                                      ==> real_le_double(x * y,z) ;
    @*/
  /* @ assert \is_finite(x) && \is_finite(y) && 
    @     !\no_overflow(\Double,\Down,-y) && \sign(y) == \Negative &&
    @     !\no_overflow(\Double,\Down,x*a) ==> real_le_double(x * y,z) ;
    @*/
  /* @ assert \is_finite(x) && \is_finite(y) && 
    @     !\no_overflow(\Double,\Down,-y) && \sign(y) == \Negative &&
    @     \no_overflow(\Double,\Down,x*a) &&
    @     !\no_overflow(\Double,\Down,-b)  ==> real_le_double(x * y,z) ;
    @*/
  /* @ assert \is_finite(x) && \is_finite(y) && 
    @     !\no_overflow(\Double,\Down,-y) && \sign(y) == \Negative &&
    @     \no_overflow(\Double,\Down,x*a) &&
    @     \no_overflow(\Double,\Down,-b) ==> real_le_double(x * y,z);
    @*/
  /* @ assert \is_finite(x) && \is_finite(y) && 
    @     \no_overflow(\Double,\Down,-y) &&
    @     \no_overflow(\Double,\Down,x*a) && 
    @     \no_overflow(\Double,\Down,-b) ==> real_le_double(x * y,z) ;
    @*/
  
  return z;
}


double zl, zu;

/*@ predicate is_interval(double xl, double xu) = 
  @       (\is_finite(xl) || \is_minus_infinity(xl)) 
  @       &&
  @       (\is_finite(xu) || \is_plus_infinity(xu));
  @*/

/*@ requires is_interval(xl,xu) && is_interval(yl,yu);
  @ ensures is_interval(zl,zu);
  @ ensures \forall real a,b; 
  @    in_interval(a,xl,xu) && in_interval(b,yl,yu) ==>
  @    in_interval(a+b,zl,zu);    
  @*/
void add(double xl, double xu, double yl, double yu)
{
  zl = xl + yl;
  /* @ assert 
    @  \forall real a,b; 
    @    in_interval(a,xl,xu) && in_interval(b,yl,yu) ==>
    @      double_le_real(zl,a+b)  ;
    @*/
  zu = -((-xu) - yu);
  /* @ assert caseuii: \is_infinite(xu) && \is_infinite(yu) ==>
    @  \forall real a,b; 
    @    in_interval(a,xl,xu) && in_interval(b,yl,yu) ==>
    @      real_le_double(a+b,zu)  ;
    @*/
  /* @ assert caseuif: \is_infinite(xu) && \is_finite(yu) ==>
    @  \forall real a,b; 
    @    in_interval(a,xl,xu) && in_interval(b,yl,yu) ==>
    @      real_le_double(a+b,zu)  ;
    @*/
  /* @ assert caseufi: \is_finite(xu) && \is_infinite(yu) ==>
    @  \forall real a,b; 
    @    in_interval(a,xl,xu) && in_interval(b,yl,yu) ==>
    @      real_le_double(a+b,zu)  ;
    @*/
  /* @ assert caseufff: \is_finite(xu) && \is_finite(yu) && \is_infinite(zu) ==>
    @  \forall real a,b; 
    @    in_interval(a,xl,xu) && in_interval(b,yl,yu) ==>
    @      real_le_double(a+b,zu)  ;
    @*/
  /* @ assert caseufff: \is_finite(xu) && \is_finite(yu) && \is_finite(zu) ==>
    @  \forall real a,b; 
    @    in_interval(a,xl,xu) && in_interval(b,yl,yu) ==>
    @      real_le_double(a+b,zu)  ;
    @*/
}



/* 
Local Variables:
compile-command: "LC_ALL=C make interval_arith"
End:
*/