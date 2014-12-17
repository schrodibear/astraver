

/*@ requires rowB > 0 && colB > 0  ;

  @ requires (\valid(b+ (0..rowB-1)) && (\forall integer  k; 0 <= k < rowB ==> \valid(b[k] +(0..colB-1) ) ));

  @ requires (\valid(c+ (0..rowB-1)) && (\forall integer  k; 0 <= k < rowB ==> \valid(c[k] +(0..colB-1) ) ));

  @ ensures  \forall integer i; \forall integer j;  (0 <= i < rowB && 0 <=j < colB)  ==> (c[i][j] == (a!=0 || b[i][j]!=0));

  @*/

int** or_scalar(float a,float** b,int rowB,int colB,int **c)

{

    int i=0,j=0;

/*@ loop invariant   (0 <= i <= rowB) && (\forall integer l;  \forall integer k; (0<=l<colB && 0 <= k <i) ==>

  @             c[k][l]  == (a!=0 || b[k][l]!=0)) ;

  @ loop variant   rowB-i;

  @*/

    while ( i < rowB )

    {

    j=0;

/*@ loop invariant   (0 <= j <= colB) && (\forall integer k;  (0<=k<j) ==>

      @             c[i][k]  == (a!=0 || b[i][k]!=0)) ;

          @ loop variant   colB-j;

          @*/

        while ( j<colB)

        {

            c[i][j]= (a!=0) || (b[i][j]!=0);

            j++;

        }

    /*@ assert  \forall integer k;  0<=k<colB ==>  (c[i][k]  ==  (a!=0 || b[i][k]!=0)) ; */

        i++;

    }

    return c;

}



/*@ requires rowB > 0 && colB > 0  ;

  @ requires (\valid(b+ (0..rowB-1)) && (\forall integer  k; 0 <= k < rowB ==> \valid(b[k] +(0..colB-1) ) ));

  @ requires (\valid(c+ (0..rowB-1)) && (\forall integer  k; 0 <= k < rowB ==> \valid(c[k] +(0..colB-1) ) ));

  @ ensures  \forall integer i; \forall integer j;  (0 <= i < rowB && 0 <=j < colB)  ==> (c[i][j] == (b[i][j]==a));

  @*/

int** equal_scalar(float a,float** b,int rowB,int colB,int **c)

{

    int i=0,j=0;

/*@ loop invariant   (0 <= i <= rowB) && (\forall integer l;  \forall integer k; (0<=l<colB && 0 <= k <i) ==>

  @             c[k][l]  == (b[k][l]==a)) ;

  @ loop variant   rowB-i;

  @*/

    while ( i < rowB )

    {

    j=0;

/*@ loop invariant   (0 <= j <= colB) && (\forall integer k;  (0<=k<j) ==>

      @             c[i][k]  == (b[i][k]==a)) ;

          @ loop variant   colB-j;

          @*/

        while ( j<colB)

        {

            c[i][j]= (b[i][j] == a);

            j++;

        }

    /*@ assert  \forall integer k;  0<=k<colB ==>  (c[i][k]  ==  (b[i][k]==a)) ; */

        i++;

    }

    return c;

}

