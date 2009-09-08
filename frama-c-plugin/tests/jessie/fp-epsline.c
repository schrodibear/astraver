/* run.config
   COMMENT: todo
   DONTRUN:
 */


#pragma JessieFloatModel(strict)

// #include <float.h>

// BUG a corriger
//@ logic integer signr(real x) = x >= 0.0 ? 1 : -1 ;

// @ logic int sign(real x)

// @ axiom sign_pos : \forall real x; x >= 0.0 => sign(x) == 1

// @ axiom sign_neg : \forall real x; x < 0.0 => sign(x) == -1
 

// Sign (0 is positive)
/*@ requires \round_error(x) <= M ;
  @ ensures \result != 0 ==> \result == signr(\exact(x)) ;
  @*/
double sign(double x, double M) {
  if (x >= M)
    return 1;
  if (x <= -M)
    return -1;
  return 0;
}

#include <float.h>

const double M22 = DBL_EPSILON*128;
/*@ global invariant M22_value: M22 == 0x1p-45; */

/*@ requires 
  @   \round_error(sx) == 0 &&
  @   \round_error(sy) == 0 &&
  @   \round_error(vx) == 0 &&
  @   \round_error(vy) == 0 &&
  @   \abs(sx) <= 100.0 && 
  @   \abs(sy) <= 100.0 && 
  @   \abs(vx) <= 1.0 && 
  @   \abs(vy) <= 1.0 ;
  @ ensures
  @    \result != 0 
  @      ==> \result == signr(\exact(sx)*\exact(vx)+\exact(sy)*\exact(vy))
  @            * signr(\exact(sx)*\exact(vy)-\exact(sy)*\exact(vx)) ;
  @*/
double eps_line(double sx, double sy, 
	     double vx, double vy) {
  return sign(sx*vx+sy*vy, M22 )*sign(sx*vy-sy*vx, M22 );
}

/*int break_symm(double sx, double sy, double sz) {
  if (sx < 0 || (sx == 0 && sy < 0)) 
    return 1;
  return -1;
  }*/
