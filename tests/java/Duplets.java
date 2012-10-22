/*
COST Verification Competition. vladimir@cost-ic0701.org

Challenge 3: Two equal elements

Given: An integer array a of length n+2 with n>=2. It is known that at
least two values stored in the array appear twice (i.e., there are at
least two duplets).

Implement and verify a program finding such two values.

You may assume that the array contains values between 0 and n-1.
*/


class Integer {
    int value;
    /*@ ensures this.value == a;
      @*/
    Integer(int a) {
        value = a;
    }
}

class Pair {
    int x,y;
    /*@ ensures this.x == a && this.y == b;
      @*/
    Pair(int a,int b) {
        x = a; y = b;
    }
}

class Quadruple {
    int x,y,z,t;
    /*@ ensures this.x == a && this.y == b &&
      @         this.z == c && this.t == d;
      @*/
    Pair(int a,int b,int c,int d) {
        x = a; y = b; z = c; t = d;
    }
}

/* equality between an integer and a possibly null Integer object */
/*@ predicate eq_opt{L}(integer x, Integer o) =
  @   o != null && x == o.value;
  @*/

/* A duplet in array a is a pair of indexes (i,j) in the bounds of array
   a such that a[i] = a[j] */
/*@ predicate is_duplet{L}(int a[], integer i, integer j) =
  @    0 <= i < j < a.length && a[i] == a[j];
  @*/

class Duplets {

    /* duplet(a) returns the indexes (i,j) of a duplet in a.
     * moreover, if except is not null, the value of this duplet must
     * be different from it.
     */
    /*@ requires 2 <= a.length &&
      @   \exists integer i j;
      @     is_duplet(a,i,j) && ! eq_opt(a[i],except) ;
      @ ensures
      @   is_duplet(a,\result.x,\result.y) &&
      @   ! eq_opt(a[\result.x],except); 
      @*/
    Pair duplet(int a[], Integer except) {
        /*@ loop_invariant
          @  \forall integer k l; 0 <= k < i && k < l < a.length ==>
          @    ! eq_opt(a[k],except) ==> ! is_duplet(a,k,l);
          @ loop_variant a.length - i;
          @*/
        for(int i=0; i <= a.length - 2; i++) {
            int v = a[i];
            if (except != null && except.value != v) {
                /*@ loop_invariant
                  @   \forall integer l; i < l < j ==> ! is_duplet(a,i,l);
                  @ loop_variant a.length - j;
                  @*/
                for (int j=i+1; j < a.length; j++) {
                    if (a[j] == v) {
                        return new Pair(i, j);
                    }
                }
            }
        }
        // assert \forall integer i j; ! is_duplet(a,i,j);
        //@ assert false;
        return null;
    }


    /* requires 4 <= a.length && \exists integer i j k l;
      @   is_duplet(a,i,j) && is_duplet(a,k,l) && a[i] != a[k];
      @ ensures is_duplet(a,\result.x,\result.y) &&
      @   is_duplet(a,\result.z,\result.t) &&
      @   a[\result.x] != a[\result.z];
      @*/
    Quadruple duplets(int a[]) {
        Pair p = duplet(a,null);
        Pair q = duplet(a,new Integer(a[p.x]));
        return new Quadruple(p.x,p.y,q.x,q.y);
    }
   

}

/*
Local Variables:
compile-command: "make Duplets.why3ide"
End:
*/

