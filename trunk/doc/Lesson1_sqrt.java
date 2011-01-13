/*@ requires x >= 0;
  @ ensures 
  @   \result >= 0 && \result * \result <= x 
  @   && x < (\result + 1) * (\result + 1);
  @*/
public static int sqrt(int x);
