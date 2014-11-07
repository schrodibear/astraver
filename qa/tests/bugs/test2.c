

typedef unsigned int gfp_t;

struct test_struct
{
	int a, b;
};

void test(void)
{
	struct test_struct *t;
	
        /*t = kmalloc(sizeof(struct test_struct), 0);*/
        
        t = kzalloc(sizeof(struct test_struct), 0);
}


