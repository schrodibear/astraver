/*@ requires x >= 0;
  @ ensures 
  @   \result >= 0 && \result * \result <= x 
  @   && x < (\result + 1) * (\result + 1);
  @*/
public static int sqrt(int x) {
    int count = 0, sum = 1;
    while (sum <= x) { 
	count++;
	sum = sum + 2*count+1;
    }
    return count;
}   
