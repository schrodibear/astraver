
typedef int my_type;

#define my_const	((my_type)1024)

void f(my_type n)
{
    if (n < my_const) {
	//@ assert n < my_const;
    }
}

