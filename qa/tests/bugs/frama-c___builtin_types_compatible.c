#define BUILD_BUG_ON(condition) ((void)sizeof(char[1 - 2*!!(condition)]))

#define __same_type(a, b) __builtin_types_compatible_p(typeof(a), typeof(b))

struct page {
	int a, b;
        int arr[];
};

enum e1 { e1, e2 };
enum e2 { e21, e22 };

typedef enum e1 e1t;
typedef enum e2 e2t;

void copy_highpage(struct page *to, struct page *from)
{
        BUILD_BUG_ON(!__same_type((to), struct page *)); 
        BUILD_BUG_ON(!__same_type((to->arr), int[5]));
        BUILD_BUG_ON(!__same_type(enum e1, enum e2));
        BUILD_BUG_ON(!__same_type(e1t, e2t));
        int a, b, c, d, e, f;
        a = __builtin_types_compatible_p(const int, volatile int);
        //@assert a == 1;
        b = __builtin_types_compatible_p(e1t, volatile unsigned int);
        //@assert b == 1;
        c = __builtin_types_compatible_p(e1t *, volatile unsigned int * const);
        //@assert c == 1;
        d = __builtin_types_compatible_p(int, char *);
        //@assert d == 0;
        e = __builtin_types_compatible_p(int[44], int[]);
        //@assert e == 1;
        f = __builtin_types_compatible_p(struct page *, struct page **);
        //@assert f == 0;
}

