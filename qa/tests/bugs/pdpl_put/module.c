#define __compiler_offsetof(a,b) __builtin_offsetof(a,b)

#define offsetof(TYPE,MEMBER) __compiler_offsetof(TYPE,MEMBER)

#define rcu_head callback_head

#define call_rcu call_rcu_sched

#define container_of(ptr,type,member) ({ const typeof( ((type *)0)->member ) *__mptr = (ptr); (type *)( (char *)__mptr - offsetof(type,member) );})

typedef unsigned short __u16;

typedef unsigned int __u32;

typedef unsigned long long __u64;

typedef unsigned char __u8;

typedef struct {
 int counter;
} atomic_t;

struct callback_head {
 struct callback_head *next;
 void (*func)(struct callback_head *head);
};

typedef __u16 uint16_t;

typedef __u32 uint32_t;

typedef __u64 uint64_t;

typedef __u8 uint8_t;
//------------------------------------------------------------------------------

// ensures ! \valid(p);
void kfree(const void *p);

/*@ terminates \false;
    assigns \nothing;
 */
void panic(const char *fmt, ...);

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
    assigns v->counter;
    ensures v->counter == \old(v->counter) - 1;
  */
extern /*static inline*/ void atomic_dec(atomic_t *v);

/*@ requires \valid(v);
    assigns v->counter;
    ensures v->counter == \old(v->counter) + 1;
  */
extern /*static inline*/ void atomic_inc(atomic_t *v);

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


extern void call_rcu_sched(struct callback_head *head, void (*func)(struct callback_head *rcu));
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
    struct rcu_head rcu;


} PDP_LABEL_T;

typedef struct PDP_LABEL_T PDPL_T;
//------------------------------------------------------------------------------

/*@ axiomatic PdplFree {
    predicate pdpl_valid_free{L}(PDPL_T *l) =
       \valid(l) && \offset_min(l) == 0 &&
       \typeof(l->catso64) <: \type(char*) &&
       (l->catso64 == \null || \valid(((char *)l->catso64)+(0..l->catso64_size)) && \offset_min(l->catso64) == 0) &&
       (l->roles   == \null || \valid(l->roles)  && \offset_min(l->roles)  == 0) &&
       (l->aroles  == \null || \valid(l->aroles) && \offset_min(l->aroles) == 0);

    }
 */

/*  requires \valid(l) && \offset_min(l) == 0;
    requires \typeof(l->catso64) <: \type(char*);
    requires l->catso64 == \null || \valid(((char *)l->catso64)+(0..l->catso64_size)) && \offset_min(l->catso64) == 0;
    requires l->roles   == \null || \valid(l->roles)  && \offset_min(l->roles)  == 0;
    requires l->aroles  == \null || \valid(l->aroles) && \offset_min(l->aroles) == 0;
    assigns *l;
    ensures !\valid(((char *)l->catso64)+(0..l->catso64_size));
    ensures !\valid(l->roles+(0..l->roles_cnt));
    ensures !\valid(l->aroles+(0..l->aroles_cnt));
    ensures !\valid(l);
 */
/*@ requires pdpl_valid_free(l);
    assigns *l;
    ensures !pdpl_valid_free(l);
 */
static void pdpl_free(PDPL_T* l)
{
    if(l->catso64) _pdp_free(l->catso64);

    if(l->roles) _pdp_free(l->roles);
    if(l->aroles) _pdp_free(l->aroles);

    _pdp_free(l);
}

/*@ axiomatic ContainterOf {
    logic PDPL_T *container_of_PDPL_T{L}(struct rcu_head *rcu);

    axiom ret1{L}:
       \forall struct rcu_head *rcu;
          \let l = container_of_PDPL_T{L}(rcu);
          &(l->rcu) == rcu;

    axiom ret2{L}:
       \forall PDPL_T *l;
          l == container_of_PDPL_T{L}(&(l->rcu));

    axiom only_one{L}:
       \forall struct rcu_head *rcu1;
       \forall struct rcu_head *rcu2;
          rcu1 == rcu2 ==>
             container_of_PDPL_T{L}(rcu1) == container_of_PDPL_T{L}(rcu2);
    }
 */

/*@ requires \valid(rcu);
    requires \valid(container_of_PDPL_T(rcu));
    requires container_of_PDPL_T(rcu)->ucnt.counter == 0;
    requires pdpl_valid_free(container_of_PDPL_T(rcu));
    assigns *container_of_PDPL_T(rcu);
    ensures !pdpl_valid_free(container_of_PDPL_T(rcu));
 */
static void _pdpl_free(struct rcu_head *rcu)
{
    PDPL_T *l= container_of(rcu,PDPL_T,rcu);
    //@ assert l == container_of_PDPL_T(rcu);

    if( atomic_read(&l->ucnt) != 0 ) panic("put_pdpl sees %p with usage %d\n", l, atomic_read(&l->ucnt));
    pdpl_free(l);
}

/* requires \valid(l) && \offset_min(l) == 0;
    requires \valid(&(l->ucnt));
    requires l->catso64 == \null ||
             \typeof(l->catso64) <: \type(char*) && \valid(((char *)l->catso64)+(0..l->catso64_size)) && \offset_min(l->catso64) == 0;
    requires l->roles   == \null || \valid(l->roles)  && \offset_min(l->roles)  == 0;
    requires l->aroles  == \null || \valid(l->aroles) && \offset_min(l->aroles) == 0;
    assigns l->ucnt.counter;
    ensures l->ucnt.counter == \old(l->ucnt.counter) - 1;
*/
/*
void pdpl_put(const PDPL_T* l)
{
    PDPL_T *ncl=(PDPL_T*)l;


    D("cnt %d",atomic_read(&(ncl->ucnt)));
    if(! atomic_dec_and_test(&(ncl->ucnt)) ) return;

    call_rcu(&ncl->rcu,_pdpl_free);



}
*/
