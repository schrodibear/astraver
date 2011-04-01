public static int sqrt(int x) {
    int count = 0, sum = 1;
    /*@ loop_invariant 
      @   count >= 0 && x >= count*count &&
      @   sum == (count+1)*(count+1);
      @ loop_variant x - sum;
      @*/
    while (sum <= x) { 
	count++;
	sum = sum + 2*count+1;
    }
    return count;
}   

