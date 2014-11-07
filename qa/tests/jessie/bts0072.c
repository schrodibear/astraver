void myfun(int p){
    p = 1;
    /*@ requires p==1;
      @ ensures \old(p)==p-1;
      @*/
    p = 2;
}

