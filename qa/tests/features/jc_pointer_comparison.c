struct subs {
	int a;
};

struct s {
	struct subs subs;
};

struct ps {
	struct subs *psubs;
};

struct subfun {
	int (*f)(int);
};

//@ assigns \nothing;
extern void *malloc(unsigned long);

//@ assigns \nothing;
extern int f(int );

int main(void)
{
	int a;
	int *pa = malloc(sizeof (int));
	struct subs subs;
	struct s s;
	struct ps ps;
	struct subfun subfun;
	struct subs *psubs = malloc(sizeof (struct subs));
	struct s *p_s = malloc(sizeof (struct s));
	struct ps *pps = malloc(sizeof (struct ps));
	struct subfun *psubfun = malloc(sizeof (struct subfun));

        subfun.f = f;
	psubfun-> f = &f;

        //@ assert (void *)&a != (void *)&subs;
        //@ assert &a != pa;
	//@ assert (void *)&a != (void *)&s;
        //@ assert (void *)&a != (void *)&ps;
        //@ assert (void *)&a != (void *)&subfun;
        
	//@ assert &a != &(subs.a);
        //@ assert (void *)&s.subs == (void *)&s;
        //@ assert (void *)&a != (void *)&(s.subs);
	//@ assert &a != &(s.subs.a);
	//@ assert (void *)&a != (void *)&(pps->psubs);
        //@ assert (void *)&a != (void *)&(subfun.f);

	//@ assert (void *)&a != (void *)psubs;
	//@ assert (void *)&a != (void *)pps;
	//@ assert (void *)&a != (void *)&subfun;

	pps = &ps;
 	pps->psubs = &s.subs;
	//@ assert pps->psubs == &s.subs;
	//@ assert ps.psubs == &s.subs;
	//@ assert (void *)&a != (void *)subfun.f;
	//@ assert (void *)&a != (void *)psubfun->f;
	//@ assert (void *)&a != (void *)&f;
	//@ assert subfun.f != &f;

	//@ assert pps->psubs + 1 == &s.subs + 1;
	//@ assert pps->psubs + 1 != &p_s->subs + 1;
}
