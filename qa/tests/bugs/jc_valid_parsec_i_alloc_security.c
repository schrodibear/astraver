#define ENOMEM 12

#define NULL ((void *)0)

#define ___GFP_FS 0x80u

#define ___GFP_IO 0x40u

#define ___GFP_WAIT 0x10u

#define __force 

#define __GFP_FS ((__force gfp_t)___GFP_FS)

#define __GFP_IO ((__force gfp_t)___GFP_IO)

#define __GFP_WAIT ((__force gfp_t)___GFP_WAIT)

#define GFP_KERNEL (__GFP_WAIT | __GFP_IO | __GFP_FS)

typedef unsigned int gfp_t;


typedef int __kernel_clockid_t;

typedef unsigned int __kernel_gid32_t;

typedef long long __kernel_loff_t;

typedef long __kernel_long_t;

typedef int __kernel_pid_t;

typedef unsigned short __kernel_sa_family_t;

typedef int __kernel_timer_t;

typedef unsigned int __kernel_uid32_t;

typedef unsigned long __kernel_ulong_t;

typedef void __restorefn_t(void);

typedef __signed__ short __s16;

typedef __signed__ int __s32;

typedef __signed__ long long __s64;

typedef __signed__ char __s8;

typedef void __signalfn_t(int);

typedef unsigned short __u16;

typedef unsigned int __u32;

typedef unsigned long long __u64;

typedef unsigned char __u8;

typedef struct {
 long counter;
} atomic64_t;

typedef struct {
 int counter;
} atomic_t;

typedef unsigned long blkcnt_t;

typedef _Bool bool;

typedef signed short s16;

typedef signed int s32;

typedef signed long long s64;

typedef unsigned long sector_t;


typedef unsigned short u16;

typedef unsigned int u32;

typedef unsigned long long u64;

typedef unsigned char u8;

typedef unsigned short umode_t;

typedef __kernel_gid32_t gid_t;

typedef __s32 int32_t;

typedef __kernel_loff_t loff_t;

typedef u64 netdev_features_t;

typedef enum netdev_tx netdev_tx_t;


typedef __kernel_pid_t pid_t;

typedef __kernel_uid32_t projid_t;

typedef enum rx_handler_result rx_handler_result_t;

typedef __kernel_sa_family_t sa_family_t;

typedef __kernel_uid32_t uid_t;

typedef __u16 uint16_t;

typedef __u32 uint32_t;

typedef __u64 uint64_t;

typedef __u8 uint8_t;

struct inode {
   void *i_security;
};


//------------------------------------------------------------------------------

extern /*static inline*/ void *kmalloc(size_t size, gfp_t flags) ;


//------------------------------------------------------------------------------

    #define ASSERT(p) do{ }while(0)

	#define T(fmt,arg...) do{ }while(0)

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

typedef struct {
//	uint32_t	 flags;


    const PDPL_T *l;
    int l_errno; /* fetching label errno */












///void * mac; ///

} parsec_inode_security_t;


//------------------------------------------------------------------------------


//@ ghost enum {SUCCESS, FAILURE} outcome_i_alloc_security;
/*@ requires \valid(i);
    requires i->i_security == \null;
    //requires \typeof(i->i_security) <: \type(parsec_inode_security_t *);
    assigns outcome_i_alloc_security, i->i_security;
    behavior SUCCESS:
        ensures outcome_i_alloc_security == SUCCESS ==>
            \valid((parsec_inode_security_t *)i->i_security) &&
            \offset_min((parsec_inode_security_t *) (i->i_security)) == 0     &&
            ((parsec_inode_security_t *) (i->i_security))->l         == \null &&
            ((parsec_inode_security_t *) (i->i_security))->l_errno   == 0     &&
            \result == 0;
    behavior FAILURE:
        ensures outcome_i_alloc_security == FAILURE ==>
            i->i_security == \null &&
            \result == -ENOMEM;
    complete behaviors;
 */
int parsec_i_alloc_security(struct inode *i)
{
    parsec_inode_security_t *is;
    T("Enter");
    ASSERT(i);

    is=kmalloc(sizeof(parsec_inode_security_t),GFP_KERNEL);
    //@ ghost if (!is) outcome_i_alloc_security = FAILURE;
    if(!is) return -ENOMEM;
    //@ ghost outcome_i_alloc_security = SUCCESS;






    is->l=NULL;
    is->l_errno=0;

    i->i_security=is;
    T("return 0");
    return 0;
}

