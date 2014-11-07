#define ACCESS_ONCE(x) (*(volatile const typeof(x) *)&(x))

#define DEVPTS_SUPER_MAGIC 0x1cd1

#define EINVAL 22

#define ENODATA 61

#define ENOMEM 12

#define ENOSYS 38

#define EPERM 1

#define MAY_EXEC 0x00000001

#define MAY_READ 0x00000004

#define MAY_WRITE 0x00000002

#define MEM_MAJOR 1

#define MINORBITS 20

#define NULL ((void *)0)

#define PIPEFS_MAGIC 0x50495045

#define PROC_SUPER_MAGIC 0x9fa0

#define SOCKFS_MAGIC 0x534F434B

#define SYSFS_MAGIC 0x62656572

#define S_IFCHR 0020000

#define S_IFMT 00170000

#define TTYAUX_MAJOR 5

#define ___GFP_FS 0x80u

#define ___GFP_IO 0x40u

#define ___GFP_WAIT 0x10u

#define __force 

#define __kernel 

#define __rcu 

#define rcu_dereference_sparse(p,space) 

#define rcu_lockdep_assert(c,s) do { } while (0)

#define read_barrier_depends() do { } while (0)

#define unlikely(x) (x)

#define MAJOR(dev) ((unsigned int) ((dev) >> MINORBITS))

#define MINORMASK ((1U << MINORBITS) - 1)

#define S_ISCHR(m) (((m) & S_IFMT) == S_IFCHR)

#define __GFP_FS ((__force gfp_t)___GFP_FS)

#define __GFP_IO ((__force gfp_t)___GFP_IO)

#define __GFP_WAIT ((__force gfp_t)___GFP_WAIT)

#define __rcu_dereference_protected(p,c,space) ({ rcu_lockdep_assert(c, "suspicious rcu_dereference_protected()" " usage"); rcu_dereference_sparse(p, space); ((typeof(*p) __force __kernel *)(p)); })

#define smp_read_barrier_depends() read_barrier_depends()

#define GFP_KERNEL (__GFP_WAIT | __GFP_IO | __GFP_FS)

#define MINOR(dev) ((unsigned int) ((dev) & MINORMASK))

#define __rcu_dereference_check(p,c,space) ({ typeof(*p) *_________p1 = (typeof(*p)*__force )ACCESS_ONCE(p); rcu_lockdep_assert(c, "suspicious rcu_dereference_check()" " usage"); rcu_dereference_sparse(p, space); smp_read_barrier_depends(); ((typeof(*p) __force __kernel *)(_________p1)); })

#define rcu_dereference_protected(p,c) __rcu_dereference_protected((p), (c), __rcu)

#define rcu_dereference_check(p,c) __rcu_dereference_check((p), rcu_read_lock_held() || (c), __rcu)

#define rcu_dereference(p) rcu_dereference_check(p, 0)

#define __task_cred(task) rcu_dereference((task)->real_cred)

//#define current get_current()

#define current_cred() rcu_dereference_protected(current->cred, 1)

#define current_cred_xxx(xxx) ({ current_cred()->xxx; })

#define get_current_cred() (current->cred)

#define current_euid() (current_cred_xxx(euid))

#define current_fsuid() (current_cred_xxx(fsuid))

#define     ENOMSG          42

#define SIZE_MAX        (~(size_t)0)
#define INT_MAX         ((int)(~0U>>1))

enum pid_type
{
 PIDTYPE_PID,
 PIDTYPE_PGID,
 PIDTYPE_SID,
 PIDTYPE_MAX
};

typedef int __kernel_clockid_t;

typedef unsigned int __kernel_gid32_t;

typedef long long __kernel_loff_t;

typedef long __kernel_long_t;

typedef int __kernel_pid_t;

typedef unsigned short __kernel_sa_family_t;

typedef int __kernel_timer_t;

typedef unsigned int __kernel_uid32_t;

typedef unsigned long __kernel_ulong_t;

typedef __signed__ short __s16;

typedef __signed__ int __s32;

typedef __signed__ long long __s64;

typedef __signed__ char __s8;

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

typedef _Bool bool;

typedef unsigned gfp_t;

typedef signed short s16;

typedef signed int s32;

typedef signed long long s64;

typedef unsigned long sector_t;

typedef unsigned short u16;

typedef unsigned int u32;

typedef unsigned long long u64;

typedef unsigned char u8;

typedef unsigned short umode_t;

struct hlist_node {
 struct hlist_node *next, **pprev;
};

struct list_head {
 struct list_head *next, *prev;
};

struct llist_node {
 struct llist_node *next;
};

typedef __kernel_long_t __kernel_clock_t;

typedef __u32 __kernel_dev_t;

typedef __kernel_ulong_t __kernel_size_t;

typedef __kernel_long_t __kernel_ssize_t;

typedef __kernel_long_t __kernel_time_t;

typedef atomic64_t atomic_long_t;

typedef __kernel_gid32_t gid_t;

typedef __s32 int32_t;

typedef struct kernel_cap_struct {
 __u32 cap[2];
} kernel_cap_t;

typedef __kernel_pid_t pid_t;

typedef __kernel_uid32_t uid_t;

typedef __u16 uint16_t;

typedef __u32 uint32_t;

typedef __u64 uint64_t;

typedef __u8 uint8_t;

struct hlist_bl_head {
 struct hlist_bl_node *first;
};

struct hlist_head {
 struct hlist_node *first;
};

struct plist_head {
 struct list_head node_list;
};

struct plist_node {
 int prio;
 struct list_head prio_list;
 struct list_head node_list;
};

//typedef __kernel_size_t size_t;

typedef __kernel_ssize_t ssize_t;

typedef __kernel_time_t time_t;

struct pid
{
 atomic_t count;
 unsigned int level;
};

typedef struct spinlock {
} spinlock_t;

struct lockref {
        //union {
                struct {
                        spinlock_t lock;
                        unsigned int count;
                };
        //};
};

struct thread_info {
 struct exec_domain *exec_domain;
 __u32 flags;
 __u32 status;
 __u32 cpu;
 int preempt_count;
 void *sysenter_return;
 unsigned long lowest_stack;
 unsigned int sig_on_uaccess_error:1;
 unsigned int uaccess_err:1;
};

typedef struct {
 spinlock_t lock;
} seqlock_t;

struct mutex {
 atomic_t count;
 spinlock_t wait_lock;
};

struct thread_struct {
 unsigned long sp0;
 unsigned long sp;
 unsigned long usersp;
 unsigned short es;
 unsigned short ds;
 unsigned short fsindex;
 unsigned short gsindex;
 unsigned short ss;
 unsigned long fs;
 unsigned long gs;
 unsigned long debugreg6;
 unsigned long ptrace_dr7;
 unsigned long cr2;
 unsigned long trap_nr;
 unsigned long error_code;
 unsigned long *io_bitmap_ptr;
 unsigned long iopl;
 unsigned io_bitmap_max;
};

typedef struct {
 gid_t val;
} kgid_t;

typedef struct {
 uid_t val;
} kuid_t;

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
 void *security;
};

struct super_block {
 unsigned long s_flags;
 unsigned long s_magic;
 struct dentry *s_root;
 int s_count;
 atomic_t s_active;
 void *s_security;
 char s_id[32];
 u8 s_uuid[16];
 void *s_fs_info;
 unsigned int s_max_links;
 u32 s_time_gran;
 char *s_subtype;
 char *s_options;
};

struct sock {
  unsigned long sk_flags;
 void *sk_security;
};

typedef __kernel_dev_t dev_t;

struct inode {
 umode_t i_mode;
 unsigned short i_opflags;
 kuid_t i_uid;
 kgid_t i_gid;
 unsigned int i_flags;
 void *i_security;
 unsigned long i_ino;
 spinlock_t i_lock;
 struct super_block *i_sb;
 dev_t i_rdev;
 const struct inode_operations *i_op;
 unsigned short i_bytes;
 unsigned int i_blkbits;
 unsigned long i_state;
 struct mutex i_mutex;
 unsigned long dirtied_when;
 u64 i_version;
 atomic_t i_count;
 atomic_t i_dio_count;
 atomic_t i_writecount;
 void *i_private;
};

struct inode_operations {
 ssize_t (*getxattr) (struct dentry *, const char *, void *, size_t);
};

struct dentry {
 unsigned int d_flags;
 struct dentry *d_parent;
 struct lockref d_lockref;
 struct inode *d_inode;
 unsigned char d_iname[32];
 struct super_block *d_sb;
 unsigned long d_time;
 void *d_fsdata;
};

struct file {
 //struct path f_path;
 struct inode *f_inode;
 spinlock_t f_lock;
 atomic_long_t f_count;
 unsigned int f_flags;
 const struct cred *f_cred;
 u64 f_version;
 void *f_security;
 void *private_data;
};

struct socket {
 ;
 short type;
 ;
 unsigned long flags;
 struct sock *sk;
};

struct task_struct {
 volatile long state;
 void *stack;
 atomic_t usage;
 unsigned int flags;
 unsigned int ptrace;
 struct llist_node wake_entry;
 int on_cpu;
 int on_rq;
 int prio, static_prio, normal_prio;
 unsigned int rt_priority;
 unsigned char fpu_counter;
 unsigned int btrace_seq;
 unsigned int policy;
 int nr_cpus_allowed;
  struct list_head tasks;
 int exit_state;
 int exit_code, exit_signal;
 int pdeath_signal;
 unsigned int jobctl;
 unsigned int personality;
 unsigned did_exec:1;
 unsigned in_execve:1;
 unsigned in_iowait:1;
 unsigned no_new_privs:1;
 unsigned sched_reset_on_fork:1;
 unsigned sched_contributes_to_load:1;
 pid_t pid;
 pid_t tgid;
 pid_t *set_child_tid;
 pid_t *clear_child_tid;
 const struct cred *real_cred;
 const struct cred *cred;
 char comm[16];
  u32 audit_ctx[2];
};

