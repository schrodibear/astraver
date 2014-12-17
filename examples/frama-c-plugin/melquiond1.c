
// high-part mul
unsigned mul(unsigned, unsigned);

unsigned max(unsigned, unsigned);

unsigned sqr(unsigned X)
{
	unsigned absX, E2, Cnan, Csmall, Clarge_or_nan, Cspec, T2, M, F, c, mu, H, L, G, T1, b;
	absX = X & 0x7fffffff;
	E2 = (X >> 22) & 0x1fe;
	Cnan = absX > 0x7f800000;
	Csmall = E2 <= 102;
	Clarge_or_nan = E2 >= 382;
	Cspec = Csmall || Clarge_or_nan;
	if (Cspec) {
		if (Csmall) return 0; // r = +0
		else {
			if (Cnan) return 0x7fc00000; // r = qNaN
			else return 0x7f800000; } // r = +oo
	} else { // generic case
		T2 = X & 0xff;
		M = (X << 8) | 0x80000000;
		F = 128 - E2;
		c = M > 0xb504f333;
		mu = max(c, F);
		H = mul(M, M);
		L = H >> (mu + 7);
		G = H >> (mu + 6);
		T1 = H << (26 - mu);
		b = (G & 1) && ((L & 1) | (T1 | T2));
		return (((mu - F) << 23) + L) + b;
	}
}
