/*@ requires a > 0 && b > 0 && c > 0;
    ensures -1 <= \result <= 0 || 2 <= \result <= 4 || \result == 6;
    ensures (a + b > c && a + c > b && b + c > a) <==> \result != -1;
    ensures (a*a + b*b == c*c || a*a + c*c == b*b || a*a == c*c + b*b) <==> (\result == 6 || \result == 4);
    ensures (a == b == c) <==> \result == 3;
    ensures (a == b != c || a == c != b || b == a != c) <==> (\result == 2 || \result == 6);
*/
int triangle(int a, int b, int c);


#include <limits.h>

/*@ ensures \result == 4; */
int test01(void) {
	return triangle(3, 4, 5) + triangle(3, 4, 6);
}

/*@ ensures \result == -3; */
int test02(void) {
	return triangle(1, 1, 100) + triangle(1, 100, 1) + triangle(100, 1, 1);
}

/*@ ensures \result == -1; */
int test03(void) {
	return triangle(1, 2, 3);
}

/*@ ensures \result == 8; */
int test04(void) {
	return triangle(1, 100, 100) *
		triangle(100, 1, 100) *
		triangle(100, 100, 1);
}

/*@ ensures \result == 3; */
int test05(void) {
	return triangle(INT_MAX, INT_MAX, INT_MAX);
}

/*@ requires a > 0 && b > 0 && c > 0;
    ensures \result != 6; */
int test06(int a, int b, int c) {
	return triangle(a, b, c);
}

/*@ requires a > 0 && b > 0 && c > 0;
    ensures \result != -1; */
int lemma(int a, int b, int c) {
	if (triangle(a, b, c) != -1
		&& a <= INT_MAX-1 && b <= INT_MAX-1 && c <= INT_MAX-1) {
		return triangle(a+1, b+1, c+1);
	} else {
		return 0;
	}
}
