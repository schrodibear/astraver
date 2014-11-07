struct s {
	_Bool b;
	int i;
};

_Bool btest(void)
{
	return 1;
}

int
main(int argc, char **argv)
{
	struct s s;
	s.i = 1;
	s.b = 0;
	//@ assert s.b == 0;
	//@ assert sizeof (struct s) == 1;
	s.i = sizeof (struct s);
	s.i = sizeof s;
	return btest();
}

