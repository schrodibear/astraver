
#pragma JessieFloatModel(multirounding)
//#pragma JessieIntegerModel(math)


//@ logic integer l_sign(real x) = (x >= 0.0) ? 1 : -1;


/*@ requires e1<= x-\exact(x) <= e2 && -0x1p+1022 <= e1 <= 0 &&
  @          0<= e2 <=0x1p+1023     && \abs(x)<=0x1p+1023 ;
  @                                
  @ ensures (\result != 0 ==> \result == l_sign(\exact(x))) &&
  @          \abs(\result) <= 1 ;
  @*/
int sign(double x, double e1, double e2) {
  
  if (x > e2)
    return 1;
  if (x < e1)
    return -1;
  return 0;
}

 
/*@ requires 
  @   sx == \exact(sx) &&
  @   sy == \exact(sy) &&
  @   vx == \exact(vx) &&
  @   vy == \exact(vy) &&
  @   \abs(sx) <= 100.0 && 
  @   \abs(sy) <= 100.0 && 
  @   \abs(vx) <= 1.0 && 
  @   \abs(vy) <= 1.0; 
  @ ensures
  @    \result != 0 
  @      ==> \result == l_sign(\exact(sx)*\exact(vx)+\exact(sy)*\exact(vy))
  @            * l_sign(\exact(sx)*\exact(vy)-\exact(sy)*\exact(vx));
  @*/

int eps_line(double sx, double sy, 
	     double vx, double vy) {
  int s1,s2;

  s1=sign(sx*vx+sy*vy, -0x1.9000000001ap-45,0x1.9000000001ap-45);

  /*@ assert \abs(s1) <= 1 && 
    @ (s1 != 0 ==> s1 == l_sign(\exact(sx)*\exact(vx)
    @                          +\exact(sy)*\exact(vy))); 
    @*/   
  s2=sign(sx*vy-sy*vx, -0x1.9000000001ap-45, 0x1.9000000001ap-45);

  /*@ assert \abs(s2) <= 1 &&
    @ (s2 != 0 
    @   ==> s2 == l_sign(\exact(sx)*\exact(vy)
    @                          -\exact(sy)*\exact(vx))); 
    @*/
  
  return s1*s2;
}

/* 
Local Variables:
compile-command: "LC_ALL=C make eps_line"
End:
*/
