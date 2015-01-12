#define rcu_head callback_head

typedef unsigned int __kernel_gid32_t;

typedef long __kernel_long_t;

typedef unsigned int __kernel_uid32_t;

typedef __signed__ int __s32;

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

typedef unsigned short u16;

typedef unsigned int u32;

typedef unsigned char u8;

struct assoc_array {
 struct assoc_array_ptr *root;
 unsigned long nr_leaves_on_tree;
};

struct callback_head {
 struct callback_head *next;
 void (*func)(struct callback_head *head);
};

struct hlist_node {
 struct hlist_node *next, **pprev;
};

struct keyring_index_key {
 struct key_type *type;
 const char *description;
 size_t desc_len;
};

struct list_head {
 struct list_head *next, *prev;
};

struct rb_node {
 unsigned long __rb_parent_color;
 struct rb_node *rb_right;
 struct rb_node *rb_left;
};

typedef __kernel_long_t __kernel_time_t;

typedef u8 __ticket_t;

typedef u16 __ticketpair_t;

typedef atomic64_t atomic_long_t;

typedef __kernel_gid32_t gid_t;

typedef __s32 int32_t;

typedef struct kernel_cap_struct {
 __u32 cap[2];
} kernel_cap_t;

typedef __kernel_uid32_t uid_t;

typedef __u16 uint16_t;

typedef __u32 uint32_t;

typedef __u64 uint64_t;

typedef __u8 uint8_t;

struct uid_gid_map {
 u32 nr_extents;
 struct uid_gid_extent {
  u32 first;
  u32 lower_first;
  u32 count;
 } extent[5];
};

struct unnamed {
  __ticketpair_t head_tail;
};

struct __raw_tickets {
  __ticket_t head, tail;
} tickets;

typedef struct arch_spinlock {
 struct unnamed tickets;
 int d;
} arch_spinlock_t;

typedef uint32_t key_perm_t;

typedef int32_t key_serial_t;

typedef gid_t kgid_t;

typedef uid_t kuid_t;

typedef __kernel_time_t time_t;

typedef struct raw_spinlock {
 arch_spinlock_t raw_lock;
} raw_spinlock_t;

struct group_info {
 atomic_t usage;
 int ngroups;
 int nblocks;
 kgid_t small_block[32];
 kgid_t *blocks[0];
};

struct user_namespace {
 struct uid_gid_map uid_map;
 struct uid_gid_map gid_map;
 struct uid_gid_map projid_map;
 atomic_t count;
 struct user_namespace *parent;
 int level;
 kuid_t owner;
 kgid_t group;
 unsigned int proc_inum;
};

struct rw_semaphore {
 long count;
 raw_spinlock_t wait_lock;
 struct list_head wait_list;
};

struct key {
 atomic_t usage;
 key_serial_t serial;
 union {
  struct list_head graveyard_link;
  struct rb_node serial_node;
 };
 struct rw_semaphore sem;
 struct key_user *user;
 void *security;
 union {
  time_t expiry;
  time_t revoked_at;
 };
 time_t last_used_at;
 kuid_t uid;
 kgid_t gid;
 key_perm_t perm;
 unsigned short quotalen;
 unsigned short datalen;
 unsigned long flags;
 union {
  struct keyring_index_key index_key;
  struct {
   struct key_type *type;
   char *description;
  };
 };
 union {
  struct list_head link;
  unsigned long x[2];
  void *p[2];
  int reject_error;
 } type_data;
 union {
  union {
   unsigned long value;
   void *rcudata;
   void *data;
   void *data2[2];
  } payload;
  struct assoc_array keys;
 };
};

struct user_struct {
 atomic_t __count;
 atomic_t processes;
 atomic_t files;
 atomic_t sigpending;
 atomic_t inotify_watches;
 atomic_t inotify_devs;
 atomic_long_t epoll_watches;
 unsigned long mq_bytes;
 unsigned long locked_shm;
 struct key *uid_keyring;
 struct key *session_keyring;
 struct hlist_node uidhash_node;
 kuid_t uid;
 atomic_long_t locked_vm;
};

struct cred {
 atomic_t usage;
 kuid_t uid;
 kgid_t gid;
 kuid_t suid;
 kgid_t sgid;
 kuid_t euid;
 kgid_t egid;
 kuid_t fsuid;
 kgid_t fsgid;
 unsigned securebits;
 kernel_cap_t cap_inheritable;
 kernel_cap_t cap_permitted;
 kernel_cap_t cap_effective;
 kernel_cap_t cap_bset;
 unsigned char jit_keyring;
 struct key *session_keyring;
 struct key *process_keyring;
 struct key *thread_keyring;
 struct key *request_key_auth;
 void *security;
 struct user_struct *user;
 struct user_namespace *user_ns;
 struct group_info *group_info;
 struct callback_head rcu;
};
//------------------------------------------------------------------------------


//------------------------------------------------------------------------------

typedef uint64_t	PDP_CAT_T;

typedef uint8_t		PDP_ILEV_T;

typedef uint8_t		PDP_LEV_T;

typedef struct PDP_ROLE_T /* struct role for subjects and objects*/
{
	uint64_t    seed;	//inode
	uint32_t    uid;	//uid_t (for subjects)
	uint8_t     access;	//mode mask (for objects)
} PDP_ROLE_T;

typedef uint16_t	PDP_TYPE_T;

typedef uint32_t	parsec_cap_t;

typedef struct PDP_ROLES_T /*  role label for subjects and objects*/
{
    PDP_ROLE_T*     roles;
    uint32_t        roles_cnt;

    PDP_ROLE_T*     aroles;
    uint32_t        aroles_cnt;

    atomic_t        ucnt;
    struct rcu_head rcu;


} PDP_LROLES_T;

typedef struct {
	parsec_cap_t	cap_effective;
	parsec_cap_t	cap_permitted;
	parsec_cap_t	cap_inheritable;
} parsec_caps_t;

typedef struct PDP_LABEL_T /* mac_role label for subjects and objects */
{
    PDP_LEV_T       lev;
    PDP_ILEV_T      ilev;
    PDP_CAT_T       cat;
    PDP_TYPE_T      type;

    void*           catso64;
    uint32_t        catso64_size;
    
    PDP_ROLE_T*		roles;
    uint32_t		roles_cnt;

    PDP_ROLE_T*		aroles;
    uint32_t		aroles_cnt;

    PDP_LROLES_T*	lroles;
    uint32_t		lroles_cnt;


    atomic_t        ucnt;
    struct rcu_head rcu;


} PDP_LABEL_T;

typedef struct PDP_LABEL_T 	PDPL_T;

typedef struct {
	uint32_t	flags;


	const PDPL_T *l;



	parsec_caps_t	caps;






} parsec_security_t;

typedef parsec_security_t       parsec_task_security_t;
//------------------------------------------------------------------------------

static inline parsec_task_security_t* CRED_SEC(const struct cred* c) { return (parsec_task_security_t *)(c->security); }

//@ assigns \nothing;
int main()
{
  struct arch_spinlock a;
  struct unnamed u;
  if (&u == 0 || u.head_tail == 0) {
    return -1;
  }
  a.d = 0;
  tickets.head = 0;
  __ticketpair_t i = 0;
  struct assoc_array aa;
  struct assoc_array_ptr ap;
  struct callback_head cbh;
  struct cred cr;
  struct group_info gi;
  struct hlist_node hln;
  struct kernel_cap_struct kcs;
  struct key k;
  struct keyring_index_key kik;
  struct key_type kt;
  struct key_user ku;
  struct list_head lh;
  struct PDP_LABEL_T PLT;
  struct PDP_ROLES_T PRT;
  struct PDP_ROLE_T PRT1;
  struct raw_spinlock rs;
  struct __raw_tickets rts;
  struct rb_node rn;
  struct rcu_head rh;
  struct roler;
  struct rw_semaphore rws;
  struct uid_gid_extent uide;
  struct uid_gid_map ugm;
  struct user_namespace un;
  struct user_struct us;

  parsec_task_security_t* ptst = CRED_SEC(&cr);
  return 0;
}
