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

//typedef __kernel_size_t size_t;


//------------------------------------------------------------------------------

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
extern /*static inline*/ int atomic_dec_and_test(atomic_t *v);

/*@ requires \valid(v);
    assigns \nothing;
    ensures \result == v->counter;
  */
extern /*static inline*/ int atomic_read(const atomic_t *v);

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
            // UNSUPPORTED: \block_length(\result) == size &&
            \valid((char *)\result+(0..size));
 */
extern /*static inline*/ void *kmalloc(size_t size, gfp_t flags);

/*@ assigns \result \from size;
    ensures \result == \null ||
               // UNSUPPORTED: \block_length(\result) == size &&
               \valid((char *)\result+(0..size)) &&
               memset((char *)\result, 0, size);
 */
extern /*static inline*/ void *kzalloc(size_t size, gfp_t flags);

extern void *memcpy(void *to, const void *from, size_t len);

//------------------------------------------------------------------------------

	#define D(fmt,arg...) do{ }while(0);

#define PARSEC_PACKED __attribute__((aligned(1),packed))

    #define PDP_KRNL(x) x

    #define PDP_KRNL_ARG(x) , x

#define _pdp_free(p) kfree(p)

#define _pdp_alloc(s,f) kmalloc(s,f)

#define _pdp_zalloc(s,f) kzalloc(s,f)

#define SIZE_MAX        (~(size_t)0)

typedef uint64_t	PDP_CAT_T;

typedef uint8_t		PDP_ILEV_T;

typedef uint8_t		PDP_LEV_T;

typedef struct PDP_RAW_LBL_H_T
{
    uint16_t	ver;
    uint16_t	type;
    uint8_t		lev;
    uint8_t		ilev;
    uint64_t	cat;
    uint32_t    catso64_size;
    uint32_t    roles_cnt;
    uint32_t    aroles_cnt;
}PARSEC_PACKED PDP_RAW_LBL_H_T;

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



/*@ logic integer pdp_roles_size{L}(size_t cnt) = cnt*sizeof(PDP_ROLE_T);
*/
/*@ requires cnt < (SIZE_MAX / sizeof(PDP_ROLE_T));
    ensures \result == cnt*sizeof(PDP_ROLE_T);
*/
static inline size_t pdp_roles_size(size_t cnt) { return cnt*sizeof(PDP_ROLE_T); }



/*@ logic integer _pdpl_raw_size{L}(PDP_RAW_LBL_H_T* rl) = 
          (sizeof(PDP_RAW_LBL_H_T) + 
           rl->catso64_size + 
           pdp_roles_size(rl->aroles_cnt) +
           pdp_roles_size(rl->roles_cnt));
*/
/*@ requires \valid(rl);
    requires rl->aroles_cnt < (SIZE_MAX / sizeof(PDP_ROLE_T));
    requires rl->roles_cnt < (SIZE_MAX / sizeof(PDP_ROLE_T));
    requires _pdpl_raw_size(rl) < SIZE_MAX;
    ensures \result == _pdpl_raw_size(rl);
*/
static inline size_t _pdpl_raw_size(const PDP_RAW_LBL_H_T* rl) { return sizeof(PDP_RAW_LBL_H_T)+rl->catso64_size+pdp_roles_size(rl->aroles_cnt)+pdp_roles_size(rl->roles_cnt); }



//@ ghost enum {SUCCESS, FAILURE} outcome_pdpl_get_new;
/*@ assigns \result;
    assigns outcome_pdpl_get_new;
    behavior SUCCESS:
        ensures outcome_pdpl_get_new == SUCCESS ==>
            \result != \null && \valid(\result) &&
            \result->lev  == 0 &&
            \result->ilev == 0 &&
            \result->cat  == 0 &&
            \result->type == 0 &&
            \result->catso64 == \null && \result->catso64_size == 0 &&
            \result->roles   == \null && \result->roles_cnt    == 0 &&
            \result->aroles  == \null && \result->aroles_cnt   == 0 &&
            \result->ucnt.counter == 1;
    behavior FAILURE:
        ensures outcome_pdpl_get_new == FAILURE ==> \result == \null;
    complete behaviors;
*/
PDPL_T* pdpl_get_new(gfp_t f)
{




    PDPL_T* l;//=_pdp_zalloc(sizeof(PDPL_T), f);

    //@ ghost if (!l) outcome_pdpl_get_new = FAILURE;
    if(!l) return l;
    //@ ghost outcome_pdpl_get_new = SUCCESS;

    PDP_KRNL( atomic_set(&(l->ucnt),1) );

    return l;
}



/*@ requires \valid(l) && \offset_min(l) == 0;
    requires \valid(&(l->ucnt));
    requires l->catso64 == \null ||
             \typeof(l->catso64) <: \type(char*) && \valid(((char *)l->catso64)+(0..l->catso64_size)) && \offset_min(l->catso64) == 0;
    requires l->roles   == \null || \valid(l->roles)  && \offset_min(l->roles)  == 0;
    requires l->aroles  == \null || \valid(l->aroles) && \offset_min(l->aroles) == 0;
    assigns l->ucnt.counter;
    ensures l->ucnt.counter == \old(l->ucnt.counter) - 1;
*/
void pdpl_put(const PDPL_T* l)
{
    PDPL_T *ncl=(PDPL_T*)l;


    D("cnt %d",atomic_read(&(ncl->ucnt)));
    if(! atomic_dec_and_test(&(ncl->ucnt)) ) return;


    if(ncl->catso64) _pdp_free(ncl->catso64);

    if(ncl->roles) _pdp_free(ncl->roles);
    if(ncl->aroles) _pdp_free(ncl->aroles);

    _pdp_free(ncl);
}



PDPL_T* pdpl_get_from_raw(const void *raw, size_t size PDP_KRNL_ARG(gfp_t f))
{
    const void *p;
    PDPL_T* l;
    const PDP_RAW_LBL_H_T *rl=raw;

    if(size<sizeof(PDP_RAW_LBL_H_T)) return NULL;

    if(rl->ver!=0x1) return NULL;

    if( size < (_pdpl_raw_size(rl)) ) return NULL;

    l=pdpl_get_new(PDP_KRNL(f));
    if(!l) return l;

    if(rl->catso64_size)
    {
        if(  !( l->catso64 = _pdp_alloc(rl->catso64_size, f) )  ) goto pdpl_put_l;
    }else l->catso64=NULL;

    if(rl->aroles_cnt)
    {
        l->aroles=_pdp_alloc( pdp_roles_size(rl->aroles_cnt), f);
        if( !l->aroles ) goto pdpl_put_l;
    }else l->aroles=NULL;

    if(rl->roles_cnt)
    {
        l->roles=_pdp_alloc( pdp_roles_size(rl->roles_cnt), f);
        if( !l->roles ) goto pdpl_put_l;
    }else l->roles=NULL;

    l->lev=rl->lev;
    l->ilev=rl->ilev;
    l->cat=rl->cat;
    l->type=rl->type;

    p=(const void *)raw+sizeof(PDP_RAW_LBL_H_T);

    l->catso64_size=rl->catso64_size;
    //if(l->catso64_size) memcpy((void *)l->catso64,(void *)p,l->catso64_size);
    p+=l->catso64_size;

    l->aroles_cnt=rl->aroles_cnt;
    if(l->aroles_cnt) memcpy(l->aroles,(PDP_ROLE_T *)p,pdp_roles_size(l->aroles_cnt));
    p+=pdp_roles_size(l->aroles_cnt);

    l->roles_cnt=rl->roles_cnt;
    if(l->roles_cnt) memcpy(l->roles,(PDP_ROLE_T *) p,pdp_roles_size(l->roles_cnt));

    return l;

pdpl_put_l:
    pdpl_put(l);
    return NULL;
}

