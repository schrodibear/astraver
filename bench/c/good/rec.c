
/* C recursive function */

/*@ requires x >= 0 assigns \nothing (* variant x *) ensures \result == 0 */ 
int f(int x) {
  if (x == 0) 
    return 0;
  else
    return f(x - 1);
}

