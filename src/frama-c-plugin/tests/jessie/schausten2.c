
#pragma JessieIntegerModel(math)

typedef struct s1 { unsigned int mantissa; int exponent; };


/*@ lemma shift_prop: \forall integer x,y;
      y >= 8 ==>
      (x << 8) * (1 << (y-8)) == x * (1 << y);
*/

/*@ requires \valid(e);
  @ requires 0 < e->mantissa < 10;
  @ requires 10 < e->exponent < 20;
  @ ensures 
  @   e->mantissa * (1 << e->exponent) == 
  @       \old(e->mantissa * (1 << e->exponent));
*/
int sizetype_normalize(struct s1* e) {
     unsigned int min_mantissa = 1 << 21;
     if (e->mantissa < min_mantissa) {
       e->mantissa <<= 8;
       e->exponent -= 8;
   }

   return 0;
}
