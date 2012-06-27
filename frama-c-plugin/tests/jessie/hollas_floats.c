 #pragma JessieFloatModel(math)

//@ lemma rp: \forall real x; x > 0.0 ==> 1.0/x > 0.0;

/*@ requires r1 > 0.0 && r2 > 0.0;
    ensures \result > 0.0;
*/
float r_seq(float r1, float r2) {
	return r1+r2;
}


/*@ requires r1 > 0.0 && r2 > 0.0;
    ensures \result > 0.0;
*/
float r_par(float r1, float r2) {
	return 1.0 / (1.0/r1 + 1.0/r2);
}


int main() {
	float r1, r2, r3, r_ges, tmp;

	r1 = 10.0; r2 = 20.0; r3 = 30.0;
	tmp = r_par(r2, r3);
	//@assert tmp > 0.0;
	r_ges = r_seq(r1, tmp);
	//@ assert r_ges > 0.0;
	return 0;
}
