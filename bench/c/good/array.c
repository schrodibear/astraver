
int t[3][3];

//@ requires \valid_index(t,1) && \valid_index(t[1],2)
int getcell() { return t[1][2];  }
