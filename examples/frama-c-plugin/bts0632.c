//@ ensures \result == EQ;
int ftest(int EQ) {
    return EQ;
}
/* Observed similar problems for:
	AND
	FORALL
	offset_min
	integer_of_int32
Observed no problems for:
	DEFPRED
	BG_PUSH
*/

//@ ensures \result == real_constant_0_0e;
double g(double real_constant_0_0e) {
    return 0.0;
}
