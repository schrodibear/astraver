
/*
    Define a predicate div(a,b), meaning "a divides b",
    and declare some basic axiomatic properties.
*/
/*@ axiomatic Euklid {
    predicate div(integer a,integer b) = (0 < a && 0 <= b && b%a == 0);
    axiom A1:
	\forall integer a, b, c;
	     b >= c && div(a,b) && div(a,c) ==> div(a,b-c);
    axiom A2:
	\forall integer a, b, c;
	     b >= c && div(a,c) && div(a,b-c) ==> div(a,b);
}
*/



/*@ 
    requires A > 0 && B > 0;
    ensures  \forall integer i; div(i,A) && div(i,B) <==> div(i,\result);
*/
int gcd(int A,int B)
{
    int const a = A, b = B;

    /*@ loop invariant a > 0 && b > 0;
        loop invariant \forall integer i;
		       div(i,a) && div(i,b) <==> div(i,A) && div(i,B);
        loop variant   a + b;
    */
    while (a != b)
        if (a > b)
             a -= b;
        else
             b -= a;
    return a;
}
