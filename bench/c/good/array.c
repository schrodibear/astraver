
int t[3][3];

//@ requires \valid_index(t,1) && \valid_index(t[1],2)
int getcell() { return t[1][2];  }

/*@ predicate valid_dim2(int** t, int i, int j, int k, int l)
    { \valid_range(t,i,j) &&
    \forall int n; i <= n <= j => \valid_range(t[n],k,l) } */
