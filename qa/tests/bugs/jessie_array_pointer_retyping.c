
void *malloc (unsigned long s);

int main()
{
	void *a[5];
	a[0] = malloc(sizeof (int));
	*((int *)a[0]) = 5;
	return 0;
}
