    #define ASSERT(p) do{ }while(0)

	#define D(fmt,arg...) do{ }while(0);

#define FUSE_SUPER_MAGIC 0x65735546

#define MCAP_TO_MASK(x) (1<<(x))

#define PARSEC_CAP_CHMAC 3 /* 8 */

#define PARSEC_CAP_FILE_CAP 0 /* 1 */

#define PARSEC_CAP_IGNMACCAT 5 /* 20 */

#define PARSEC_CAP_IGNMACLVL 4 /* 10 */

#define PARSEC_CAP_PRIV_SOCK 8 /* 100 */

#define PARSEC_CAP_READSEARCH 9 /* 200 */

#define PARSEC_CAP_UPDATE_ATIME 7 /* 80 */

#define PARSEC_MAGIC 0x0a5c5f

#define PARSEC_PACKED __attribute__((aligned(1),packed))

#define PDPT_CCNR 0x01

#define PDPT_EHOLE 0x04

    #define PDP_KRNL(x) x

    #define PDP_KRNL_ARG(x) , x

	#define T(fmt,arg...) do{ }while(0)

#define PARSEC_CAP_FS_MASK ( MCAP_TO_MASK(PARSEC_CAP_FILE_CAP) | MCAP_TO_MASK(PARSEC_CAP_CHMAC) | MCAP_TO_MASK(PARSEC_CAP_IGNMACLVL) | MCAP_TO_MASK(PARSEC_CAP_IGNMACCAT) | MCAP_TO_MASK(PARSEC_CAP_UPDATE_ATIME) | MCAP_TO_MASK(PARSEC_CAP_READSEARCH) )

#define PARSEC_CAP_MASK ( MCAP_TO_MASK(PARSEC_CAP_PRIV_SOCK) )

    #define R_OK MAY_READ

    #define W_OK MAY_WRITE

    #define X_OK MAY_EXEC

#define _pdp_free(p) kfree(p)

#define parsec_cap_is_cap(c) (MCAP_TO_MASK(c) & PARSEC_CAP_MASK)

#define parsec_cap_is_fs_cap(c) (MCAP_TO_MASK(c) & PARSEC_CAP_FS_MASK)

#define _pdp_alloc(s,f) kmalloc(s,f)

#define _pdp_zalloc(s,f) kzalloc(s,f)

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

typedef uint32_t	parsec_cap_t;

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

typedef struct {
	parsec_cap_t	cap_effective;
	parsec_cap_t	cap_permitted;
	parsec_cap_t	cap_inheritable;
} parsec_caps_t;

extern const size_t PDPL_RAW_MIN_SIZE;

typedef struct PDP_LABEL_T PDPL_T;

extern parsec_caps_t		parsec_null_caps;

typedef struct {
//	uint32_t	 flags;


    const PDPL_T *l;
    int l_errno; /* fetching label errno */












///void * mac; ///

} parsec_inode_security_t;

typedef struct {
    uint32_t	flags;


    const PDPL_T *l;



	parsec_caps_t	caps;






} parsec_security_t;

extern const PDPL_T *PDPL_EQU;

extern const PDPL_T *PDPL_ZERO;

typedef parsec_security_t       parsec_task_security_t;

