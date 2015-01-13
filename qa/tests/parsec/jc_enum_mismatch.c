#define ATOMIC_INIT(i) { (i) }

#define NULL ((void *)0)

typedef unsigned long __kernel_ulong_t;

typedef unsigned short __u16;

typedef unsigned int __u32;

typedef unsigned long long __u64;

typedef unsigned char __u8;

typedef struct {
 int counter;
} atomic_t;

typedef unsigned gfp_t;

typedef __kernel_ulong_t __kernel_size_t;

typedef __u16 uint16_t;

typedef __u32 uint32_t;

typedef __u64 uint64_t;

typedef __u8 uint8_t;


//------------------------------------------------------------------------------

extern /*static inline*/ void *kmalloc(size_t size, gfp_t flags) ;


//------------------------------------------------------------------------------

    #define PDP_KRNL_ARG(x) , x

#define _pdp_alloc(s,f) kmalloc(s,f)

typedef uint64_t	PDP_CAT_T;

typedef uint8_t		PDP_ILEV_T;

typedef uint8_t		PDP_LEV_T;

typedef struct PDP_ROLE_T
{
    uint32_t seed;
} PDP_ROLE_T;

typedef uint16_t	PDP_TYPE_T;

typedef struct PDP_LABEL_T
{
    PDP_LEV_T lev;
    PDP_ILEV_T ilev;
    PDP_CAT_T cat;
    PDP_TYPE_T type;

    void* catso64;
    uint32_t catso64_size;

    PDP_ROLE_T* roles;
    uint32_t roles_cnt;

    PDP_ROLE_T* aroles;
    uint32_t aroles_cnt;


    atomic_t ucnt;


} PDP_LABEL_T;

typedef struct PDP_LABEL_T PDPL_T;


//------------------------------------------------------------------------------

//@ ghost static enum { SUCCESS, FAILURE } outcome_pdp_get_new;
// ghost enum outcome { SUCCESS, FAILURE };
// ghost static enum outcome outcome_pdp_get_new;

/*@ assigns outcome_pdp_get_new, \result;
    behavior FAIL:
        ensures outcome_pdp_get_new == FAILURE ==> \result == 0;
    behavior OK:
        ensures outcome_pdp_get_new == SUCCESS ==> \result->ucnt.counter == 1;
    complete behaviors;
*/
PDPL_T* pdpl_get_new(gfp_t f)
{




    PDPL_T* l=_pdp_alloc(sizeof(PDPL_T), f);

    if(!l) {
	//@ ghost outcome_pdp_get_new = FAILURE;
        return l;
    }
    //@ ghost outcome_pdp_get_new = SUCCESS;

    *l=(PDPL_T){0,0,0,0,NULL,0,NULL,0,NULL,0 PDP_KRNL_ARG(ATOMIC_INIT(1)) };

    return l;
}

