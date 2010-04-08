
#pragma JessieFloatModel(math)

//@ ghost int i_f;

/*@ requires 3 <= n <= 17;
    requires \valid_range(X,0,n);
    requires \valid_range(Y,0,n);
    requires \valid_range(V,0,n);
    
    requires X[0] == X[1];
    requires \forall integer k1, int k2; 1 <= k1 < k2 <= n ==> X[k1] < X[k2];

    assumes Y[0] == Y[1];
    assumes V[0] == V[n] == 0.0;
    assumes \forall integer k; 1 <= k <= n-1 ==> V[k] == (Y[k+1] - Y[k]) / (X[k+1] - X[k]);

    behavior small:
        assumes x < X[0];
        ensures \result == Y[0];
    
    behavior big:
        assumes x >= X[n];
        ensures \result == Y[n];

    behavior inter:
        assumes X[0] <= x < X[n];
        ensures     1 <= i_f <= n-1
                &&  \result == Y[i_f] + (x-X[i_f]) * (Y[i_f+1] - Y[i_f]) / (X[i_f+1] - X[i_f]);
*/
double InterPolate(double x, double X[], double Y[], double V[], int n) {
    int i=0;
    //@ ghost int i0;
    int m=(n+1)/2;
    
    if (x >= X[m]) i=m;
    //@ ghost i0=i;
    //@ for small: assert i==0;
    
    /*@ loop invariant i0 <= i <= n;
        loop invariant \forall integer k; i0 <= k < i ==> x >= X[i];
        for small: loop invariant i==0;
        loop variant n-i;
    */
    while ((i < n) && (x >= X[i+1])) i++;
    //@ ghost i_f=i;
    //@ for small: assert i==0;
    //@ for big: assert i==n;
    return Y[i] + (x-X[i]) * V[i];
}



/*
Local Variables: 
compile-command: "make floats_interp_math"
End: 
*/
