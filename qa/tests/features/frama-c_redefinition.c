typedef signed int int_t;

typedef int_t int_t;

typedef int_t int_t;

typedef int int_t;

int g (int_t *a);

int f(int_t a)
{
	g(&a);
}

typedef int int_t;

int g(int_t *b);

//@ assigns \nothing;
int main()
{
	int a;
	f(a);
	g(&a);
	return 0;
}
