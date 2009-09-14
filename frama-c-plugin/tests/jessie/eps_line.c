
// @ lemma a1: \forall integer x,y; x*y != 0 ==> x!=0 && y!=0;

#pragma JessieFloatModel(multirounding)
#pragma JessieIntegerModel(math)
// #pragma JessieFloatModel(strict)


//@ logic integer signe(real x) = (x >= 0.0) ? 1 : -1;



/*@ requires \abs(x-\exact(x)) <= M;
  @ ensures (\result != 0 ==> \result == signe(\exact(x))) &&
  @          \abs(\result) <= 1 ;
  @*/
int sign(double x, double M) {
   double m = -M;
  //@ assert  m == -M;
  if (x > M)
    return 1;
  if (x < m)
    return -1;
  return 0;
}

// 
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
  @      ==> \result == signe(\exact(sx)*\exact(vx)+\exact(sy)*\exact(vy))
  @            * signe(\exact(sx)*\exact(vy)-\exact(sy)*\exact(vx));
  @*/

int eps_line(double sx, double sy, 
	     double vx, double vy) {
  int s1,s2;

   s1=sign(sx*vx+sy*vy, 0x1.9000000001ap-45 );

  /*@ assert \abs(s1) <= 1 && 
      (s1 != 0 ==> s1 == signe(\exact(sx)*\exact(vx)+\exact(sy)*\exact(vy))); */   
    s2=sign(sx*vy-sy*vx, 0x1.9000000001ap-45 );

  /*@ assert \abs(s2) <= 1 &&
      (s2 != 0 ==> s2 == signe(\exact(sx)*\exact(vy)-\exact(sy)*\exact(vx))); */
  
  return s1*s2;
}

/* 
Local Variables:
compile-command: "LC_ALL=C make eps_line"
End:
*/
