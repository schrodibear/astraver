asm ("");

struct s {
	int i;
	char b;
};

asm ("nop");

//@ assigns \nothing;
extern void * malloc(unsigned long s);

//@ ensures \result == 0 ||  \result == 1 || \result == 2;
int f()
{
	register int y = 0, i;
	struct s s;
	struct s *ps1 = &s;
        struct s *ps2 = malloc(sizeof (struct s));
	asm ("nop");
	asm ("nop" : "=r" (y));
	y = 10;
	asm ("nop" : : "r" (y));
	//@ assert y == 10;
	asm ("nop" : : : "memory");
	//@ assert y == 10;
	y = 20;
	asm ("nop" : "=m" (s) : "r" (i));
	//@ assert y == 20;
	asm ("nop" : "=m" (s), "=r" (i) : "m" (s.i), [x] "r" (i), "r" (y));
	//@ assert y == 20;
	asm ("nop" : [xxx] "=m" (s), [yyy] "=r" (i) : [yy] "m" (s.b), [uu] "r" (i));
	asm ("nop" : "=m" (s), "=m" (ps2->i));
	i = 30;
	asm ("nop" : "=m" (s), [y] "=m" (ps2->i) : "r" (ps2) : "memory");
	//@ assert i == 30;
	ps2->i = 40;
	asm goto ( "jmp %l[out1]" : : [x] "m" (ps1->i), "r" (y) : : out1, out2);
	//@ assert ps2->i == 40;
	asm goto ( "jmp %l[out]" : /* no outputs */ : /* inputs */ : "memory" /* clobbers */ : out /* any labels used */ );

out:
	return 0;

out_m1:
	return -1; // Unreachable

out1:
	//@ assert ps2->i == 40;
	return 1;

out2:
	return 2;
}

int main()
{
    int r = f();
    //@ assert r != 3;
    //@ assert r != -1;
    //@ assert r > -1 && r < 3;
    //@ assert r != -1; 
}
