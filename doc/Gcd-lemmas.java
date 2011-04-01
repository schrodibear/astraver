/*@ lemma distr_right: 
  @   \forall integer x y z; x*(y+z) == (x*y)+(x*z); 
  @*/

/*@ lemma distr_left: 
  @   \forall integer x y z; (x+y)*z == (x*z)+(y*z);
  @*/

/*@ lemma distr_right_minus: 
  @   \forall integer x y z; x*(y-z) == (x*y)-(x*z); 
  @*/

/*@ lemma distr_left_minus: 
  @   \forall integer x y z; (x-y)*z == (x*z)-(y*z);
  @*/

/*@ lemma mul_comm: 
  @   \forall integer x y; x*y == y*x; 
  @*/

/*@ lemma mul_assoc: 
  @   \forall integer x y z; x*(y*z) == (x*y)*z; 
  @*/

/*@ lemma div_mod_property:
  @  \forall integer x y; 
  @    x >=0 && y > 0 ==> x%y  == x - y*(x/y);  
  @*/

/*@ lemma mod_property:
  @  \forall integer x y; 
  @    x >=0 && y > 0 ==> 0 <= x%y && x%y < y; 
  @*/

/*@ lemma gcd_zero :
  @   \forall integer a; isGcd(a,0,a) ;
  @*/

/*@ lemma gcd_property :
  @   \forall integer a b d q;
  @      b > 0 && isGcd(b,a % b,d) ==> isGcd(a,b,d) ;
  @*/

