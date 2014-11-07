//typedef unsigned long size_t;

extern /*static inline*/ void *kmalloc(size_t size, int flags) ;

void *memset(void *s, int c, size_t n);


struct test_struct
{
	int a, b;
};

void test(void)
{
	struct test_struct *t;

	t = kmalloc(sizeof(struct test_struct), 0);
}


