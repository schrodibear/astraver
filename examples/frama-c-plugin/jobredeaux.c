
/*@ ensures (\valid(\result+ (0..m-1)) && (\forall integer  k; 0 <= k < m ==> \valid(\result[k] +(0..n-1) ) )) ; */
float **allocM(int m, int n);

/*@ requires m > 0 && n > 0;
  @  assigns \nothing;
  @
  @  ensures  \result == \null || (\forall integer i; \forall integer j;
  @       0 <= i < m && 0 <= j <n ==> *(\result[i]+j)  == 1.0);
 @*/
float** ones(int m,int n)
{
    /*@ assert m > 0  && n > 0; */

    float **c = allocM(m,n);

    /*@ assert (\valid(c+ (0..m-1)) && (\forall integer  k; 0 <= k < m ==> \valid(c[k] +(0..n-1) ) )) ; */

    int i = 0;
    int j = 0;


    /*@  loop assigns *(c[0..m-1]+(0..n-1));
      @ loop invariant  (0 <= i <=m) && (\forall integer k; \forall integer q;  (0<= k < i && 0 <= q < n) ==> (*(c[k]+q) == 1.0)) ;
      @  loop variant m-i ;
      */
    for (i = 0; i<m; i++){
    /*@ assert 0<= i < m; */
    /*@ assert \valid(c[i]+(0..n-1)); */

    /*@ loop assigns  *(c[i] +(0..n-1));
      @ loop invariant (0 <= j <= n) && (\forall integer l; 0 <= l < j ==> ( *(c[i] + l)  == 1.0) );
      @ loop invariant \forall integer p; \forall integer q;  (0 <= p <i && 0 <= q < n) ==> *(c[p]+q) == \at(*(c[p]+q),Here) ;
      @ loop invariant \forall integer p; \forall integer q;  (i < p <n && 0 <= q < n) ==> *(c[p]+q) == \at(*(c[p]+q),Here) ;
      @ loop variant n-j ;
      */
        for (j = 0; j<n;j++){

        /*@ assert  0<=j < n ; */
        /*@ assert \valid(c[i]+j); */
      *(c[i] + j) = (float) 1.0;
       /*@ assert *(c[i] + j) == 1.0; */
        }
    /*@ assert \forall integer l; 0 <= l < n ==> ( *(c[i] + l)  == 1.0) ; */


    }
    return c;
} 
