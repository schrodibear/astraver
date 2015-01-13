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


#define PDP_KRNL(x) x
//------------------------------------------------------------------------------

/*@ requires \valid(v);
    assigns v->counter;
    ensures v->counter == i;
 */
extern /*static inline*/ void atomic_set(atomic_t *v, int i);


/*@ axiomatic MemSet {
    logic 𝔹 memset{L}(char *s, ℤ c, ℤ n);
    // reads s[0..n - 1];
    // Returns [true] iff array [s] contains only character [c]
   
    axiom memset_def{L}:
      \forall char *s; \forall ℤ c; \forall ℤ n;
         memset(s,c,n) <==> \forall ℤ i; 0 <= i < n ==> s[i] == c;
    }
  */
/*@ requires \valid(((char*)s)+(0..count - 1));
    assigns ((char*)s)[0..count - 1] \from c;
    assigns \result \from s;
    ensures memset((char*)s,c,count);
    ensures \result == s;
  */
void *memset(void *s, int c, size_t count);

/*@ assigns \result \from size;
    ensures \result == \null ||
            \offset_max(\result) == size && \valid((char *)\result+(0..size));
 */
extern /*static inline*/ void *kmalloc(size_t size, gfp_t flags);

/*@ assigns \result \from size;
    ensures \result == \null ||
               \offset_max(\result) == size &&
               \valid((char *)\result+(0..size)) &&
               memset((char *)\result, 0, size);
 */
extern /*static inline*/ void *kzalloc(size_t size, gfp_t flags);


//@ ghost enum {SUCCESS, FAILURE} outcome_pdpl_get_new;

/*@ 
    assigns outcome_pdpl_get_new;
    behavior SUCCESS:
        ensures outcome_pdpl_get_new == SUCCESS ==>
            \result != 0 && \valid(\result) &&
            \result->lev == 0 && \result->ilev == 0 &&
            \result->cat == 0 &&
            \result->type == 0 &&
            \result->catso64 == NULL && \result->catso64_size == 0 &&
            \result->roles  == NULL && \result->roles_cnt  == 0 &&
            \result->aroles == NULL && \result->aroles_cnt == 0 &&
            \result->ucnt.counter == 1;
    behavior FAILURE:
        ensures outcome_pdpl_get_new == FAILURE ==> \result == 0;
    complete behaviors;
*/
PDPL_T* pdpl_get_new(gfp_t f)
{



    Label:;    
    PDPL_T* l=kzalloc(sizeof(PDPL_T), f);

    //@ ghost if (!l) outcome_pdpl_get_new = FAILURE;
    if(!l) return l;

    PDP_KRNL( atomic_set(&(l->ucnt),1) );

    //@ ghost outcome_pdpl_get_new = SUCCESS;
    return l;
}

