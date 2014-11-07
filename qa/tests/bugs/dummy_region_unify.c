/*@ requires \valid(p + (0..n-1));
 */
void fff(int *p, int n) {
	p[n-1] = 0;
}

void ggg(void) {

	int p[1000];

        //@ jessie pragma (&p[0]) :> char *;
	char *q = p;
	//@ assert \base_addr(q) == q;

	//@ assert \valid(p + (0..-2));

        //@ jessie pragma q :> int *;

	fff(p, -1);
}
