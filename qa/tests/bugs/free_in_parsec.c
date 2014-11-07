typedef unsigned short __u16;

typedef unsigned int __u32;

typedef unsigned long long __u64;

typedef unsigned char __u8;

typedef struct {
 int counter;
} atomic_t;

typedef __u16 uint16_t;

typedef __u32 uint32_t;

typedef __u64 uint64_t;

typedef __u8 uint8_t;

//#define NULL ((void *) 0)
#define NULL 0

//------------------------------------------------------------------------------

void kfree(const void *);

/*@ requires \valid(v);
    assigns v->counter;
    ensures v->counter == \old(v->counter) - 1;
    behavior TRUE:
        assumes v->counter == 0;
        ensures \result == 1;
    behavior FALSE:
        assumes v->counter != 0;
        ensures \result == 0;
    complete behaviors;
    disjoint behaviors;
  */
extern /*static inline*/ int atomic_dec_and_test(atomic_t *v) ;

/*@ requires \valid(v);
    assigns \nothing;
    ensures \result == v->counter;
  */
extern /*static inline*/ int atomic_read(const atomic_t *v) ;


//------------------------------------------------------------------------------

	#define D(fmt,arg...) do{ }while(0);

#define _pdp_free(p) kfree(p)

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

/*@ requires \valid(l) && \offset_min(l) == 0;
    requires \valid(&(l->ucnt));
    requires l->catso64 == \null ||
             \typeof(l->catso64) <: \type(char *) && \valid(((char *)l->catso64)+(0..l->catso64_size)) && \offset_min(l->catso64) == 0;
    requires l->roles   == \null || \valid(l->roles)  && \offset_min(l->roles)  == 0;
    requires l->aroles  == \null || \valid(l->aroles) && \offset_min(l->aroles) == 0;
    assigns l->ucnt.counter;
    ensures l->ucnt.counter == \old(l->ucnt.counter) - 1;
*/
void pdpl_put(PDPL_T* l)
{


    D("cnt %d",atomic_read(&(l->ucnt)));
    if(! atomic_dec_and_test(&(l->ucnt)) ) return;


    if(l->catso64) _pdp_free(l->catso64);

    if(l->roles) _pdp_free(l->roles);
    if(l->aroles) _pdp_free(l->aroles);

    _pdp_free(l);
}

