#define CONFIG_BASE_SMALL 0

#define CONFIG_NODES_SHIFT 6

#define CONFIG_NR_CPUS 64

#define IFNAMSIZ 16

#define __ARCH_SI_PREAMBLE_SIZE (4 * sizeof(int))

#define rcu_head callback_head

enum { NFPROTO_NUMPROTO = 13 };

enum { __UDP_MIB_MAX = 8 };

enum { NR_MM_COUNTERS = 3 };

enum { __LINUX_MIB_MAX = 96 };

enum { __ICMP6_MIB_MAX = 6 };

enum { MAX_NESTED_LINKS = 8 };

enum { __IPSTATS_MIB_MAX = 36 };

enum { __ICMP_MIB_MAX = 28 };

enum { __RTAX_MAX = 16 };

enum { SB_FREEZE_COMPLETE = 4 };

enum { XFRM_POLICY_MAX = 3 };

enum { __TCP_MIB_MAX = 16 };

enum cgroup_subsys_id {
 CGROUP_BUILTIN_SUBSYS_COUNT,
 CGROUP_SUBSYS_COUNT = CGROUP_BUILTIN_SUBSYS_COUNT - 1 + 1
};

enum dev_pm_qos_req_type { __STUB__DEV_PM_QOS_REQ_TYPE };

enum dma_attr { DMA_ATTR_MAX = 7 };

enum dma_data_direction { __STUB__DMA_DATA_DIRECTION };

enum ethtool_phys_id_state { __STUB__ETHTOOL_PHYS_ID_STATE };

enum hrtimer_base_type { HRTIMER_MAX_CLOCK_BASES = 4 };

enum hrtimer_restart { __STUB__HRTIMER_RESTART };

enum kobj_ns_type { __STUB__KOBJ_NS_TYPE };

enum migrate_mode { __STUB__MIGRATE_MODE };

enum module_state { __STUB__MODULE_STATE };

enum netdev_tx { __STUB__NETDEV_TX };

enum perf_event_task_context { perf_nr_task_contexts = 2 };

enum pid_type
{
 PIDTYPE_PID,
 PIDTYPE_MAX = 3
};

enum pm_qos_type { __STUB__PM_QOS_TYPE };

enum quota_type { __STUB__QUOTA_TYPE };

enum rx_handler_result { __STUB__RX_HANDLER_RESULT };

enum tcp_conntrack {
 TCP_CONNTRACK_LISTEN = 9,
 TCP_CONNTRACK_TIMEOUT_MAX = 14
};

enum udp_conntrack { UDP_CT_MAX = 2 };

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

typedef struct {
    unsigned int interval;
    unsigned int timeout;
} cisco_proto;

typedef unsigned long cputime_t;

typedef struct files_struct *fl_owner_t;

typedef unsigned fmode_t;

typedef struct {
 unsigned int t391;
 unsigned int t392;
 unsigned int n391;
 unsigned int n392;
 unsigned int n393;
 unsigned short lmi;
 unsigned short dce;
} fr_proto;

typedef struct {
 unsigned int dlci;
} fr_proto_pvc;

typedef unsigned gfp_t;

typedef int (kiocb_cancel_fn)(struct kiocb *);

typedef struct {
 unsigned long seg;
} mm_segment_t;

typedef int (*notifier_fn_t)(struct notifier_block *nb,
   unsigned long action, void *data);

typedef unsigned oom_flags_t;

typedef void (percpu_ref_func_t)(struct percpu_ref *);

typedef unsigned long pgdval_t;

typedef unsigned long pgprotval_t;

typedef struct pm_message {
 int event;
} pm_message_t;

typedef long long qsize_t;

typedef struct {
 unsigned short encoding;
 unsigned short parity;
} raw_hdlc_proto;

typedef struct {
 size_t written;
 size_t count;
 union {
  char *buf;
  void *data;
 } arg;
 int error;
} read_descriptor_t;

typedef signed short s16;

typedef signed int s32;

typedef signed long long s64;

typedef unsigned long sector_t;

typedef struct seqcount {
 unsigned sequence;
} seqcount_t;

typedef struct {
 unsigned long sig[(64 / 64)];
} sigset_t;

typedef union sigval {
 int sival_int;
 void *sival_ptr;
} sigval_t;

typedef unsigned int sk_buff_data_t;

typedef enum {
 SS_FREE = 0,
 SS_UNCONNECTED,
 SS_CONNECTING,
 SS_CONNECTED,
 SS_DISCONNECTING
} socket_state;

typedef struct {
 unsigned int clock_rate;
 unsigned int clock_type;
 unsigned short loopback;
} sync_serial_settings;

typedef struct {
 unsigned int clock_rate;
 unsigned int clock_type;
 unsigned short loopback;
 unsigned int slot_map;
} te1_settings;

typedef unsigned short u16;

typedef unsigned int u32;

typedef unsigned long long u64;

typedef unsigned char u8;

typedef unsigned short umode_t;

typedef void (*work_func_t)(struct work_struct *work);

struct acpi_dev_node {
 struct acpi_device *companion;
};

struct assoc_array {
 struct assoc_array_ptr *root;
 unsigned long nr_leaves_on_tree;
};

struct bug_entry {
 signed int bug_addr_disp;
 signed int file_disp;
 unsigned short line;
 unsigned short flags;
};

struct callback_head {
 struct callback_head *next;
 void (*func)(struct callback_head *head);
};

struct dev_pm_ops {
 int (*prepare)(struct device *dev);
 void (*complete)(struct device *dev);
 int (*suspend)(struct device *dev);
 int (*resume)(struct device *dev);
 int (*freeze)(struct device *dev);
 int (*thaw)(struct device *dev);
 int (*poweroff)(struct device *dev);
 int (*restore)(struct device *dev);
 int (*suspend_late)(struct device *dev);
 int (*resume_early)(struct device *dev);
 int (*freeze_late)(struct device *dev);
 int (*thaw_early)(struct device *dev);
 int (*poweroff_late)(struct device *dev);
 int (*restore_early)(struct device *dev);
 int (*suspend_noirq)(struct device *dev);
 int (*resume_noirq)(struct device *dev);
 int (*freeze_noirq)(struct device *dev);
 int (*thaw_noirq)(struct device *dev);
 int (*poweroff_noirq)(struct device *dev);
 int (*restore_noirq)(struct device *dev);
 int (*runtime_suspend)(struct device *dev);
 int (*runtime_resume)(struct device *dev);
 int (*runtime_idle)(struct device *dev);
};

struct device_dma_parameters {
 unsigned int max_segment_size;
 unsigned long segment_boundary_mask;
};

struct dql {
 unsigned int num_queued;
 unsigned int adj_limit;
 unsigned int last_obj_cnt;
 unsigned int limit ;
 unsigned int num_completed;
 unsigned int prev_ovlimit;
 unsigned int prev_num_queued;
 unsigned int prev_last_obj_cnt;
 unsigned int lowest_slack;
 unsigned long slack_start_time;
 unsigned int max_limit;
 unsigned int min_limit;
 unsigned int slack_hold_time;
};

struct exception_table_entry {
 int insn, fixup;
};

struct file_lock_operations {
 void (*fl_copy_lock)(struct file_lock *, struct file_lock *);
 void (*fl_release_private)(struct file_lock *);
};

struct hlist_bl_node {
 struct hlist_bl_node *next, **pprev;
};

struct hlist_node {
 struct hlist_node *next, **pprev;
};

struct hlist_nulls_node {
 struct hlist_nulls_node *next, **pprev;
};

struct ifmap {
 unsigned long mem_start;
 unsigned long mem_end;
 unsigned short base_addr;
 unsigned char irq;
 unsigned char dma;
 unsigned char port;
};

struct kernel_param_ops {
 unsigned int flags;
 int (*set)(const char *val, const struct kernel_param *kp);
 int (*get)(char *buffer, const struct kernel_param *kp);
 void (*free)(void *arg);
};

struct kernel_symbol
{
 unsigned long value;
 const char *name;
};

struct keyring_index_key {
 struct key_type *type;
 const char *description;
 size_t desc_len;
};

struct kmem_cache_cpu {
 void **freelist;
 unsigned long tid;
 struct page *page;
 struct page *partial;
};

struct kmem_cache_order_objects {
 unsigned long x;
};

struct kobj_uevent_env {
 char *envp[32];
 int envp_idx;
 char buf[2048];
 int buflen;
};

struct kparam_string {
 unsigned int maxlen;
 char *string;
};

struct kset_uevent_ops {
 int (* const filter)(struct kset *kset, struct kobject *kobj);
 const char *(* const name)(struct kset *kset, struct kobject *kobj);
 int (* const uevent)(struct kset *kset, struct kobject *kobj,
        struct kobj_uevent_env *env);
};

struct list_head {
 struct list_head *next, *prev;
};

struct llist_node {
 struct llist_node *next;
};

struct lock_class_key { };

struct lock_manager_operations {
 int (*lm_compare_owner)(struct file_lock *, struct file_lock *);
 unsigned long (*lm_owner_key)(struct file_lock *);
 void (*lm_notify)(struct file_lock *);
 int (*lm_grant)(struct file_lock *, struct file_lock *, int);
 void (*lm_break)(struct file_lock *);
 int (*lm_change)(struct file_lock **, int);
};

struct mod_arch_specific
{
};

struct module_ref {
 unsigned long incs;
 unsigned long decs;
};

struct neigh_statistics {
 unsigned long allocs;
 unsigned long destroys;
 unsigned long hash_grows;
 unsigned long res_failed;
 unsigned long lookups;
 unsigned long hits;
 unsigned long rcv_probes_mcast;
 unsigned long rcv_probes_ucast;
 unsigned long periodic_gc_runs;
 unsigned long forced_gc_runs;
 unsigned long unres_discards;
};

struct net_device_stats {
 unsigned long rx_packets;
 unsigned long tx_packets;
 unsigned long rx_bytes;
 unsigned long tx_bytes;
 unsigned long rx_errors;
 unsigned long tx_errors;
 unsigned long rx_dropped;
 unsigned long tx_dropped;
 unsigned long multicast;
 unsigned long collisions;
 unsigned long rx_length_errors;
 unsigned long rx_over_errors;
 unsigned long rx_crc_errors;
 unsigned long rx_frame_errors;
 unsigned long rx_fifo_errors;
 unsigned long rx_missed_errors;
 unsigned long tx_aborted_errors;
 unsigned long tx_carrier_errors;
 unsigned long tx_fifo_errors;
 unsigned long tx_heartbeat_errors;
 unsigned long tx_window_errors;
 unsigned long rx_compressed;
 unsigned long tx_compressed;
};

struct netdev_phys_port_id {
 unsigned char id[32];
 unsigned char id_len;
};

struct new_utsname {
 char sysname[64 + 1];
 char nodename[64 + 1];
 char release[64 + 1];
 char version[64 + 1];
 char machine[64 + 1];
 char domainname[64 + 1];
};

struct nfs4_lock_info {
 struct nfs4_lock_state *owner;
};

struct pollfd {
 int fd;
 short events;
 short revents;
};

struct pt_regs {
 unsigned long r15;
 unsigned long r14;
 unsigned long r13;
 unsigned long r12;
 unsigned long bp;
 unsigned long bx;
 unsigned long r11;
 unsigned long r10;
 unsigned long r9;
 unsigned long r8;
 unsigned long ax;
 unsigned long cx;
 unsigned long dx;
 unsigned long si;
 unsigned long di;
 unsigned long orig_ax;
 unsigned long ip;
 unsigned long cs;
 unsigned long flags;
 unsigned long sp;
 unsigned long ss;
};

struct rb_node {
 unsigned long __rb_parent_color;
 struct rb_node *rb_right;
 struct rb_node *rb_left;
};

struct rlimit {
 unsigned long rlim_cur;
 unsigned long rlim_max;
};

struct sched_info {
 unsigned long pcount;
 unsigned long long run_delay;
 unsigned long long last_arrival,
      last_queued;
};

struct seccomp {
 int mode;
 struct seccomp_filter *filter;
};

struct sysv_sem {
 struct sem_undo_list *undo_list;
};

struct tracepoint_func {
 void *func;
 void *data;
};

struct u64_stats_sync {
};

struct uprobes_state {
};

struct vfsmount {
 struct dentry *mnt_root;
 struct super_block *mnt_sb;
 int mnt_flags;
};

typedef __u64 Elf64_Addr;

typedef __u16 Elf64_Half;

typedef __u32 Elf64_Word;

typedef __u64 Elf64_Xword;

typedef __u64 __addrpair;

typedef __u16 __be16;

typedef __u32 __be32;

typedef __kernel_long_t __kernel_clock_t;

typedef __u32 __kernel_dev_t;

typedef __kernel_ulong_t __kernel_size_t;

typedef __kernel_long_t __kernel_ssize_t;

typedef __kernel_long_t __kernel_time_t;

typedef __u32 __portpair;

typedef __signalfn_t *__sighandler_t;

typedef __restorefn_t *__sigrestore_t;

typedef u8 __ticket_t;

typedef u16 __ticketpair_t;

typedef __u32 __wsum;

typedef union {
 s32 lock;
 s32 write;
} arch_rwlock_t;

typedef atomic64_t atomic_long_t;

typedef atomic64_t atomic_long_unchecked_t;

typedef atomic_t atomic_unchecked_t;

typedef __kernel_clockid_t clockid_t;

typedef s32 compat_long_t;

typedef s32 compat_time_t;

typedef u32 compat_uptr_t;

typedef struct cpumask { unsigned long bits[(((CONFIG_NR_CPUS) + (8 * sizeof(long)) - 1) / (8 * sizeof(long)))]; } cpumask_t;

typedef u64 dma_addr_t;

typedef s32 dma_cookie_t;

typedef struct {
 unsigned int dlci;
 char master[IFNAMSIZ];
}fr_proto_pvc_info;

typedef struct fs_disk_quota {
 __s8 d_version;
 __s8 d_flags;
 __u16 d_fieldmask;
 __u32 d_id;
 __u64 d_blk_hardlimit;
 __u64 d_blk_softlimit;
 __u64 d_ino_hardlimit;
 __u64 d_ino_softlimit;
 __u64 d_bcount;
 __u64 d_icount;
 __s32 d_itimer;
 __s32 d_btimer;
 __u16 d_iwarns;
 __u16 d_bwarns;
 __s32 d_padding2;
 __u64 d_rtb_hardlimit;
 __u64 d_rtb_softlimit;
 __u64 d_rtbcount;
 __s32 d_rtbtimer;
 __u16 d_rtbwarns;
 __s16 d_padding3;
 char d_padding4[8];
} fs_disk_quota_t;

typedef struct fs_qfilestat {
 __u64 qfs_ino;
 __u64 qfs_nblks;
 __u32 qfs_nextents;
} fs_qfilestat_t;

typedef __kernel_gid32_t gid_t;

typedef void (*handler_t)(int, struct pt_regs *);

typedef __s32 int32_t;

typedef struct kernel_cap_struct {
 __u32 cap[2];
} kernel_cap_t;

typedef __kernel_loff_t loff_t;

typedef u64 netdev_features_t;

typedef enum netdev_tx netdev_tx_t;

typedef struct { unsigned long bits[((((1 << CONFIG_NODES_SHIFT)) + (8 * sizeof(long)) - 1) / (8 * sizeof(long)))]; } nodemask_t;

typedef struct { pgdval_t pgd; } pgd_t;

typedef struct pgprot { pgprotval_t pgprot; } pgprot_t;

typedef __kernel_pid_t pid_t;

typedef __kernel_uid32_t projid_t;

typedef enum rx_handler_result rx_handler_result_t;

typedef __kernel_sa_family_t sa_family_t;

typedef __kernel_uid32_t uid_t;

typedef __u16 uint16_t;

typedef __u32 uint32_t;

typedef __u64 uint64_t;

typedef __u8 uint8_t;

struct attribute {
 const char *name;
 umode_t mode;
};

struct cftype_set {
 struct list_head node;
 struct cftype *cfts;
};

struct cgroup_map_cb {
 int (*fill)(struct cgroup_map_cb *cb, const char *key, u64 value);
 void *state;
};

struct cgroup_name {
 struct callback_head callback_head;
 char name[];
};

struct cpu_itimer {
 cputime_t expires;
 cputime_t incr;
 u32 error;
 u32 incr_error;
};

struct cputime {
 cputime_t utime;
 cputime_t stime;
};

struct ctl_node {
 struct rb_node node;
 struct ctl_table_header *header;
};

struct desc_struct {
 union {
  struct {
   unsigned int a;
   unsigned int b;
  };
  struct {
   u16 limit0;
   u16 base0;
   unsigned base1: 8, type: 4, s: 1, dpl: 2, p: 1;
   unsigned limit: 4, avl: 1, l: 1, d: 1, g: 1, base2: 8;
  };
  struct {
   u16 offset_low;
   u16 seg;
   unsigned reserved: 8, type: 4, s: 1, dpl: 2, p: 1;
   unsigned offset_high: 16;
  } gate;
 };
};

struct dev_pm_domain {
 struct dev_pm_ops ops;
};

struct dma_attrs {
 unsigned long flags[(((DMA_ATTR_MAX) + (8 * sizeof(long)) - 1) / (8 * sizeof(long)))];
};

struct ethtool_channels {
 __u32 cmd;
 __u32 max_rx;
 __u32 max_tx;
 __u32 max_other;
 __u32 max_combined;
 __u32 rx_count;
 __u32 tx_count;
 __u32 other_count;
 __u32 combined_count;
};

struct ethtool_cmd {
 __u32 cmd;
 __u32 supported;
 __u32 advertising;
 __u16 speed;
 __u8 duplex;
 __u8 port;
 __u8 phy_address;
 __u8 transceiver;
 __u8 autoneg;
 __u8 mdio_support;
 __u32 maxtxpkt;
 __u32 maxrxpkt;
 __u16 speed_hi;
 __u8 eth_tp_mdix;
 __u8 eth_tp_mdix_ctrl;
 __u32 lp_advertising;
 __u32 reserved[2];
};

struct ethtool_coalesce {
 __u32 cmd;
 __u32 rx_coalesce_usecs;
 __u32 rx_max_coalesced_frames;
 __u32 rx_coalesce_usecs_irq;
 __u32 rx_max_coalesced_frames_irq;
 __u32 tx_coalesce_usecs;
 __u32 tx_max_coalesced_frames;
 __u32 tx_coalesce_usecs_irq;
 __u32 tx_max_coalesced_frames_irq;
 __u32 stats_block_coalesce_usecs;
 __u32 use_adaptive_rx_coalesce;
 __u32 use_adaptive_tx_coalesce;
 __u32 pkt_rate_low;
 __u32 rx_coalesce_usecs_low;
 __u32 rx_max_coalesced_frames_low;
 __u32 tx_coalesce_usecs_low;
 __u32 tx_max_coalesced_frames_low;
 __u32 pkt_rate_high;
 __u32 rx_coalesce_usecs_high;
 __u32 rx_max_coalesced_frames_high;
 __u32 tx_coalesce_usecs_high;
 __u32 tx_max_coalesced_frames_high;
 __u32 rate_sample_interval;
};

struct ethtool_drvinfo {
 __u32 cmd;
 char driver[32];
 char version[32];
 char fw_version[32];
 char bus_info[32];
 char reserved1[32];
 char reserved2[12];
 __u32 n_priv_flags;
 __u32 n_stats;
 __u32 testinfo_len;
 __u32 eedump_len;
 __u32 regdump_len;
};

struct ethtool_dump {
 __u32 cmd;
 __u32 version;
 __u32 flag;
 __u32 len;
 __u8 data[0];
};

struct ethtool_eee {
 __u32 cmd;
 __u32 supported;
 __u32 advertised;
 __u32 lp_advertised;
 __u32 eee_active;
 __u32 eee_enabled;
 __u32 tx_lpi_enabled;
 __u32 tx_lpi_timer;
 __u32 reserved[2];
};

struct ethtool_eeprom {
 __u32 cmd;
 __u32 magic;
 __u32 offset;
 __u32 len;
 __u8 data[0];
};

struct ethtool_flash {
 __u32 cmd;
 __u32 region;
 char data[128];
};

struct ethtool_modinfo {
 __u32 cmd;
 __u32 type;
 __u32 eeprom_len;
 __u32 reserved[8];
};

struct ethtool_pauseparam {
 __u32 cmd;
 __u32 autoneg;
 __u32 rx_pause;
 __u32 tx_pause;
};

struct ethtool_regs {
 __u32 cmd;
 __u32 version;
 __u32 len;
 __u8 data[0];
};

struct ethtool_ringparam {
 __u32 cmd;
 __u32 rx_max_pending;
 __u32 rx_mini_max_pending;
 __u32 rx_jumbo_max_pending;
 __u32 tx_max_pending;
 __u32 rx_pending;
 __u32 rx_mini_pending;
 __u32 rx_jumbo_pending;
 __u32 tx_pending;
};

struct ethtool_stats {
 __u32 cmd;
 __u32 n_stats;
 __u64 data[0];
};

struct ethtool_test {
 __u32 cmd;
 __u32 flags;
 __u32 reserved;
 __u32 len;
 __u64 data[0];
};

struct ethtool_ts_info {
 __u32 cmd;
 __u32 so_timestamping;
 __s32 phc_index;
 __u32 tx_types;
 __u32 tx_reserved[3];
 __u32 rx_filters;
 __u32 rx_reserved[3];
};

struct ethtool_wolinfo {
 __u32 cmd;
 __u32 supported;
 __u32 wolopts;
 __u8 sopass[6];
};

struct fiemap_extent {
 __u64 fe_logical;
 __u64 fe_physical;
 __u64 fe_length;
 __u64 fe_reserved64[2];
 __u32 fe_flags;
 __u32 fe_reserved[3];
};

struct fs_qfilestatv {
 __u64 qfs_ino;
 __u64 qfs_nblks;
 __u32 qfs_nextents;
 __u32 qfs_pad;
};

struct hlist_bl_head {
 struct hlist_bl_node *first;
};

struct hlist_head {
 struct hlist_node *first;
};

struct hlist_nulls_head {
 struct hlist_nulls_node *first;
};

struct i387_fsave_struct {
 u32 cwd;
 u32 swd;
 u32 twd;
 u32 fip;
 u32 fcs;
 u32 foo;
 u32 fos;
 u32 st_space[20];
 u32 status;
};

struct i387_fxsave_struct {
 u16 cwd;
 u16 swd;
 u16 twd;
 u16 fop;
 union {
  struct {
   u64 rip;
   u64 rdp;
  };
  struct {
   u32 fip;
   u32 fcs;
   u32 foo;
   u32 fos;
  };
 };
 u32 mxcsr;
 u32 mxcsr_mask;
 u32 st_space[32];
 u32 xmm_space[64];
 u32 padding[12];
 union {
  u32 padding1[12];
  u32 sw_reserved[12];
 };
};

struct icmp_mib {
 unsigned long mibs[__ICMP_MIB_MAX];
};

struct icmpv6_mib {
 unsigned long mibs[__ICMP6_MIB_MAX];
};

struct idr_layer {
 int prefix;
 unsigned long bitmap[((((1 << 8)) + (8 * sizeof(long)) - 1) / (8 * sizeof(long)))];
 struct idr_layer *ary[1<<8];
 int count;
 int layer;
 struct callback_head callback_head;
};

struct if_dqinfo {
 __u64 dqi_bgrace;
 __u64 dqi_igrace;
 __u32 dqi_flags;
 __u32 dqi_valid;
};

struct ifla_vf_info {
 __u32 vf;
 __u8 mac[32];
 __u32 vlan;
 __u32 qos;
 __u32 tx_rate;
 __u32 spoofchk;
 __u32 linkstate;
};

struct ipstats_mib {
 u64 mibs[__IPSTATS_MIB_MAX];
 struct u64_stats_sync syncp;
};

struct ipv6_devconf {
 __s32 forwarding;
 __s32 hop_limit;
 __s32 mtu6;
 __s32 accept_ra;
 __s32 accept_redirects;
 __s32 autoconf;
 __s32 dad_transmits;
 __s32 rtr_solicits;
 __s32 rtr_solicit_interval;
 __s32 rtr_solicit_delay;
 __s32 force_mld_version;
 __s32 mldv1_unsolicited_report_interval;
 __s32 mldv2_unsolicited_report_interval;
 __s32 use_tempaddr;
 __s32 temp_valid_lft;
 __s32 temp_prefered_lft;
 __s32 regen_max_retry;
 __s32 max_desync_factor;
 __s32 max_addresses;
 __s32 accept_ra_defrtr;
 __s32 accept_ra_pinfo;
 __s32 proxy_ndp;
 __s32 accept_source_route;
 __s32 disable_ipv6;
 __s32 accept_dad;
 __s32 force_tllao;
 __s32 ndisc_notify;
 __s32 suppress_frag_ndisc;
 void *sysctl;
};

struct kernel_vm86_regs {
 struct pt_regs pt;
 unsigned short es, __esh;
 unsigned short ds, __dsh;
 unsigned short fs, __fsh;
 unsigned short gs, __gsh;
};

struct kobj_ns_type_operations {
 enum kobj_ns_type type;
 bool (*current_may_mount)(void);
 void *(*grab_current_ns)(void);
 const void *(*netlink_ns)(struct sock *sk);
 const void *(*initial_ns)(void);
 void (*drop_ns)(void *);
};

struct kparam_array
{
 unsigned int max;
 unsigned int elemsize;
 unsigned int *num;
 const struct kernel_param_ops *ops;
 void *elem;
};

struct kref {
 atomic_t refcount;
};

union ktime {
 s64 tv64;
};

struct linux_mib {
 unsigned long mibs[__LINUX_MIB_MAX];
};

struct load_weight {
 unsigned long weight;
 u32 inv_weight;
};

struct ndmsg {
 __u8 ndm_family;
 __u8 ndm_pad1;
 __u16 ndm_pad2;
 __s32 ndm_ifindex;
 __u16 ndm_state;
 __u8 ndm_flags;
 __u8 ndm_type;
};

struct netdev_hw_addr_list {
 struct list_head list;
 int count;
};

struct netdev_tc_txq {
 u16 count;
 u16 offset;
};

struct netns_xt {
 struct list_head tables[NFPROTO_NUMPROTO];
 bool notrack_deprecated_warning;
 bool ulog_warn_deprecated;
};

struct nf_conntrack {
 atomic_t use;
};

struct nfs_lock_info {
 u32 state;
 struct nlm_lockowner *owner;
 struct list_head list;
};

struct nla_policy {
 u16 type;
 u16 len;
};

struct nlattr {
 __u16 nla_len;
 __u16 nla_type;
};

struct nlmsghdr {
 __u32 nlmsg_len;
 __u16 nlmsg_type;
 __u16 nlmsg_flags;
 __u32 nlmsg_seq;
 __u32 nlmsg_pid;
};

struct notifier_block {
 notifier_fn_t notifier_call;
 struct notifier_block *next;
 int priority;
};

struct pacct_struct {
 int ac_flag;
 long ac_exitcode;
 unsigned long ac_mem;
 cputime_t ac_utime, ac_stime;
 unsigned long ac_minflt, ac_majflt;
};

struct path {
 struct vfsmount *mnt;
 struct dentry *dentry;
};

struct percpu_ref {
 atomic_t count;
 unsigned *pcpu_count;
 percpu_ref_func_t *release;
 percpu_ref_func_t *confirm_kill;
 struct callback_head rcu;
};

struct pidmap {
       atomic_t nr_free;
       void *page;
};

struct plist_head {
 struct list_head node_list;
};

struct plist_node {
 int prio;
 struct list_head prio_list;
 struct list_head node_list;
};

struct pm_qos_flags {
 struct list_head list;
 s32 effective_flags;
};

struct pm_qos_flags_request {
 struct list_head node;
 s32 flags;
};

struct pneigh_entry {
 struct pneigh_entry *next;
 struct net *net;
 struct net_device *dev;
 u8 flags;
 u8 key[0];
};

struct qstr {
 union {
  struct {
   u32 hash; u32 len;;
  };
  u64 hash_len;
 };
 const unsigned char *name;
};

struct radix_tree_root {
 unsigned int height;
 gfp_t gfp_mask;
 struct radix_tree_node *rnode;
};

struct rb_root {
 struct rb_node *rb_node;
};

struct rps_dev_flow {
 u16 cpu;
 u16 filter;
 unsigned int last_qtail;
};

struct rps_map {
 unsigned int len;
 struct callback_head rcu;
 u16 cpus[0];
};

struct rtnl_link_stats64 {
 __u64 rx_packets;
 __u64 tx_packets;
 __u64 rx_bytes;
 __u64 tx_bytes;
 __u64 rx_errors;
 __u64 tx_errors;
 __u64 rx_dropped;
 __u64 tx_dropped;
 __u64 multicast;
 __u64 collisions;
 __u64 rx_length_errors;
 __u64 rx_over_errors;
 __u64 rx_crc_errors;
 __u64 rx_frame_errors;
 __u64 rx_fifo_errors;
 __u64 rx_missed_errors;
 __u64 tx_aborted_errors;
 __u64 tx_carrier_errors;
 __u64 tx_fifo_errors;
 __u64 tx_heartbeat_errors;
 __u64 tx_window_errors;
 __u64 rx_compressed;
 __u64 tx_compressed;
};

struct sched_avg {
 u32 runnable_avg_sum, runnable_avg_period;
 u64 last_runnable_update;
 s64 decay_count;
 unsigned long load_avg_contrib;
};

struct sched_rt_entity {
 struct list_head run_list;
 unsigned long timeout;
 unsigned long watchdog_stamp;
 unsigned int time_slice;
 struct sched_rt_entity *back;
};

struct sched_statistics {
 u64 wait_start;
 u64 wait_max;
 u64 wait_count;
 u64 wait_sum;
 u64 iowait_count;
 u64 iowait_sum;
 u64 sleep_start;
 u64 sleep_max;
 s64 sum_sleep_runtime;
 u64 block_start;
 u64 block_max;
 u64 exec_max;
 u64 slice_max;
 u64 nr_migrations_cold;
 u64 nr_failed_migrations_affine;
 u64 nr_failed_migrations_running;
 u64 nr_failed_migrations_hot;
 u64 nr_forced_migrations;
 u64 nr_wakeups;
 u64 nr_wakeups_sync;
 u64 nr_wakeups_migrate;
 u64 nr_wakeups_local;
 u64 nr_wakeups_remote;
 u64 nr_wakeups_affine;
 u64 nr_wakeups_affine_attempts;
 u64 nr_wakeups_passive;
 u64 nr_wakeups_idle;
};

struct sigpending {
 struct list_head list;
 sigset_t signal;
};

struct sock_filter {
 __u16 code;
 __u8 jt;
 __u8 jf;
 __u32 k;
};

struct static_key {
 atomic_t enabled;
};

struct task_cputime {
 cputime_t utime;
 cputime_t stime;
 unsigned long long sum_exec_runtime;
};

struct task_io_accounting {
 u64 rchar;
 u64 wchar;
 u64 syscr;
 u64 syscw;
 u64 read_bytes;
 u64 write_bytes;
 u64 cancelled_write_bytes;
};

struct task_rss_stat {
 int events;
 int count[NR_MM_COUNTERS];
};

struct taskstats {
 __u16 version;
 __u32 ac_exitcode;
 __u8 ac_flag;
 __u8 ac_nice;
 __u64 cpu_count ;
 __u64 cpu_delay_total;
 __u64 blkio_count;
 __u64 blkio_delay_total;
 __u64 swapin_count;
 __u64 swapin_delay_total;
 __u64 cpu_run_real_total;
 __u64 cpu_run_virtual_total;
 char ac_comm[32];
 __u8 ac_sched ;
 __u8 ac_pad[3];
 __u32 ac_uid ;
 __u32 ac_gid;
 __u32 ac_pid;
 __u32 ac_ppid;
 __u32 ac_btime;
 __u64 ac_etime ;
 __u64 ac_utime;
 __u64 ac_stime;
 __u64 ac_minflt;
 __u64 ac_majflt;
 __u64 coremem;
 __u64 virtmem;
 __u64 hiwater_rss;
 __u64 hiwater_vm;
 __u64 read_char;
 __u64 write_char;
 __u64 read_syscalls;
 __u64 write_syscalls;
 __u64 read_bytes;
 __u64 write_bytes;
 __u64 cancelled_write_bytes;
 __u64 nvcsw;
 __u64 nivcsw;
 __u64 ac_utimescaled;
 __u64 ac_stimescaled;
 __u64 cpu_scaled_run_real_total;
 __u64 freepages_count;
 __u64 freepages_delay_total;
};

struct tcp_mib {
 unsigned long mibs[__TCP_MIB_MAX];
};

struct timer_list {
 struct list_head entry;
 unsigned long expires;
 struct tvec_base *base;
 void (*function)(unsigned long);
 unsigned long data;
 int slack;
 int start_pid;
 void *start_site;
 char start_comm[16];
};

struct udp_mib {
 unsigned long mibs[__UDP_MIB_MAX];
};

struct uid_gid_map {
 u32 nr_extents;
 struct uid_gid_extent {
  u32 first;
  u32 lower_first;
  u32 count;
 } extent[5];
};

struct xps_map {
 unsigned int len;
 unsigned int alloc_len;
 struct callback_head rcu;
 u16 queues[0];
};

struct xsave_hdr_struct {
 u64 xstate_bv;
 u64 reserved1[2];
 u64 reserved2[5];
};

struct ymmh_struct {
 u32 ymmh_space[64];
};

typedef struct elf64_sym {
  Elf64_Word st_name;
  unsigned char st_info;
  unsigned char st_other;
  Elf64_Half st_shndx;
  Elf64_Addr st_value;
  Elf64_Xword st_size;
} Elf64_Sym;

typedef struct arch_spinlock {
 union {
  __ticketpair_t head_tail;
  struct __raw_tickets {
   __ticket_t head, tail;
  } tickets;
 };
} arch_spinlock_t;

typedef struct cpumask cpumask_var_t[1];

typedef __kernel_dev_t dev_t;

typedef int (*filldir_t)(void *, const char *, int, loff_t, u64, unsigned);

typedef struct fs_quota_stat {
 __s8 qs_version;
 __u16 qs_flags;
 __s8 qs_pad;
 fs_qfilestat_t qs_uquota;
 fs_qfilestat_t qs_gquota;
 __u32 qs_incoredqs;
 __s32 qs_btimelimit;
 __s32 qs_itimelimit;
 __s32 qs_rtbtimelimit;
 __u16 qs_bwarnlimit;
 __u16 qs_iwarnlimit;
} fs_quota_stat_t;

typedef uint32_t key_perm_t;

typedef int32_t key_serial_t;

typedef gid_t kgid_t;

typedef projid_t kprojid_t;

typedef union ktime ktime_t;

typedef uid_t kuid_t;

typedef int proc_handler (struct ctl_table *ctl, int write,
     void *buffer, size_t *lenp, loff_t *ppos);

typedef struct {
 arch_rwlock_t raw_lock;
} rwlock_t;

typedef struct siginfo {
 int si_signo;
 int si_errno;
 int si_code;
 union {
  int _pad[((128 - __ARCH_SI_PREAMBLE_SIZE) / sizeof(int))];
  struct {
   __kernel_pid_t _pid;
   __kernel_uid32_t _uid;
  } _kill;
  struct {
   __kernel_timer_t _tid;
   int _overrun;
   char _pad[sizeof( __kernel_uid32_t) - sizeof(int)];
   sigval_t _sigval;
   int _sys_private;
  } _timer;
  struct {
   __kernel_pid_t _pid;
   __kernel_uid32_t _uid;
   sigval_t _sigval;
  } _rt;
  struct {
   __kernel_pid_t _pid;
   __kernel_uid32_t _uid;
   int _status;
   __kernel_clock_t _utime;
   __kernel_clock_t _stime;
  } _sigchld;
  struct {
   void *_addr;
   short _addr_lsb;
  } _sigfault;
  struct {
   long _band;
   int _fd;
  } _sigpoll;
  struct {
   void *_call_addr;
   int _syscall;
   unsigned int _arch;
  } _sigsys;
 } _sifields;
} siginfo_t;

typedef __kernel_ssize_t ssize_t;

typedef __kernel_time_t time_t;

struct compat_robust_list {
 compat_uptr_t next;
};

struct compat_timespec {
 compat_time_t tv_sec;
 s32 tv_nsec;
};

struct dentry_operations {
 int (*d_revalidate)(struct dentry *, unsigned int);
 int (*d_weak_revalidate)(struct dentry *, unsigned int);
 int (*d_hash)(const struct dentry *, struct qstr *);
 int (*d_compare)(const struct dentry *, const struct dentry *,
   unsigned int, const char *, const struct qstr *);
 int (*d_delete)(const struct dentry *);
 void (*d_release)(struct dentry *);
 void (*d_prune)(struct dentry *);
 void (*d_iput)(struct dentry *, struct inode *);
 char *(*d_dname)(struct dentry *, char *, int);
 struct vfsmount *(*d_automount)(struct path *);
 int (*d_manage)(struct dentry *, bool);
};

struct dev_pm_qos_request {
 enum dev_pm_qos_req_type type;
 union {
  struct plist_node pnode;
  struct pm_qos_flags_request flr;
 } data;
 struct device *dev;
};

struct ethhdr {
 unsigned char h_dest[6];
 unsigned char h_source[6];
 __be16 h_proto;
};

struct ethtool_ah_espip4_spec {
 __be32 ip4src;
 __be32 ip4dst;
 __be32 spi;
 __u8 tos;
};

struct ethtool_flow_ext {
 __u8 padding[2];
 unsigned char h_dest[6];
 __be16 vlan_etype;
 __be16 vlan_tci;
 __be32 data[2];
};

struct ethtool_tcpip4_spec {
 __be32 ip4src;
 __be32 ip4dst;
 __be16 psrc;
 __be16 pdst;
 __u8 tos;
};

struct ethtool_usrip4_spec {
 __be32 ip4src;
 __be32 ip4dst;
 __be32 l4_4_bytes;
 __u8 tos;
 __u8 ip_ver;
 __u8 proto;
};

struct fiemap_extent_info {
 unsigned int fi_flags;
 unsigned int fi_extents_mapped;
 unsigned int fi_extents_max;
 struct fiemap_extent *fi_extents_start;
};

struct file_ra_state {
 unsigned long start;
 unsigned int size;
 unsigned int async_size;
 unsigned int ra_pages;
 unsigned int mmap_miss;
 loff_t prev_pos;
};

struct fs_quota_statv {
 __s8 qs_version;
 __u8 qs_pad1;
 __u16 qs_flags;
 __u32 qs_incoredqs;
 struct fs_qfilestatv qs_uquota;
 struct fs_qfilestatv qs_gquota;
 struct fs_qfilestatv qs_pquota;
 __s32 qs_btimelimit;
 __s32 qs_itimelimit;
 __s32 qs_rtbtimelimit;
 __u16 qs_bwarnlimit;
 __u16 qs_iwarnlimit;
 __u64 qs_pad2[8];
};

struct icmpmsg_mib {
 atomic_long_t mibs[512];
};

struct icmpv6_mib_device {
 atomic_long_t mibs[__ICMP6_MIB_MAX];
};

struct icmpv6msg_mib {
 atomic_long_t mibs[512];
};

struct icmpv6msg_mib_device {
 atomic_long_t mibs[512];
};

struct if_settings {
 unsigned int type;
 unsigned int size;
 union {
  raw_hdlc_proto *raw_hdlc;
  cisco_proto *cisco;
  fr_proto *fr;
  fr_proto_pvc *fr_pvc;
  fr_proto_pvc_info *fr_pvc_info;
  sync_serial_settings *sync;
  te1_settings *te1;
 } ifs_ifsu;
};

struct in6_addr {
 union {
  __u8 u6_addr8[16];
  __be16 u6_addr16[8];
  __be32 u6_addr32[4];
 } in6_u;
};

struct inet_ehash_bucket {
 struct hlist_nulls_head chain;
};

struct inetpeer_addr_base {
 union {
  __be32 a4;
  __be32 a6[4];
 };
};

struct iovec
{
 void *iov_base;
 __kernel_size_t iov_len;
};

struct kernel_param {
 const char *name;
 const struct kernel_param_ops *ops;
 u16 perm;
 s16 level;
 union {
  void *arg;
  const struct kparam_string *str;
  const struct kparam_array *arr;
 };
};

struct klist_node {
 void *n_klist;
 struct list_head n_node;
 struct kref n_ref;
};

struct kobject {
 const char *name;
 struct list_head entry;
 struct kobject *parent;
 struct kset *kset;
 struct kobj_type *ktype;
 struct sysfs_dirent *sd;
 struct kref kref;
 unsigned int state_initialized:1;
 unsigned int state_in_sysfs:1;
 unsigned int state_add_uevent_sent:1;
 unsigned int state_remove_uevent_sent:1;
 unsigned int uevent_suppress:1;
};

struct math_emu_info {
 long ___orig_eip;
 union {
  struct pt_regs *regs;
  struct kernel_vm86_regs *vm86;
 };
};

struct mm_rss_stat {
 atomic_long_t count[NR_MM_COUNTERS];
};

struct rps_dev_flow_table {
 unsigned int mask;
 struct callback_head rcu;
 struct rps_dev_flow flows[0];
};

struct scatterlist {
 unsigned long page_link;
 unsigned int offset;
 unsigned int length;
 dma_addr_t dma_address;
 unsigned int dma_length;
};

struct sched_entity {
 struct load_weight load;
 struct rb_node run_node;
 struct list_head group_node;
 unsigned int on_rq;
 u64 exec_start;
 u64 sum_exec_runtime;
 u64 vruntime;
 u64 prev_sum_exec_runtime;
 u64 nr_migrations;
 struct sched_statistics statistics;
 struct sched_entity *parent;
 struct cfs_rq *cfs_rq;
 struct cfs_rq *my_q;
 struct sched_avg avg;
};

struct seq_operations {
 void * (*start) (struct seq_file *m, loff_t *pos);
 void (*stop) (struct seq_file *m, void *v);
 void * (*next) (struct seq_file *m, void *v, loff_t *pos);
 int (*show) (struct seq_file *m, void *v);
};

struct shrink_control {
 gfp_t gfp_mask;
 unsigned long nr_to_scan;
 nodemask_t nodes_to_scan;
 int nid;
};

struct sigaction {
 __sighandler_t sa_handler;
 unsigned long sa_flags;
 __sigrestore_t sa_restorer;
 sigset_t sa_mask;
};

struct sockaddr {
 sa_family_t sa_family;
 char sa_data[14];
};

struct timespec {
 __kernel_time_t tv_sec;
 long tv_nsec;
};

struct tracepoint {
 const char *name;
 struct static_key key;
 void (*regfunc)(void);
 void (*unregfunc)(void);
 struct tracepoint_func *funcs;
};

struct work_struct {
 atomic_long_t data;
 struct list_head entry;
 work_func_t func;
};

struct xfrm_policy_hash {
 struct hlist_head *table;
 unsigned int hmask;
};

struct xps_dev_maps {
 struct callback_head rcu;
 struct xps_map *cpu_map[0];
};

struct xsave_struct {
 struct i387_fxsave_struct i387;
 struct xsave_hdr_struct xsave_hdr;
 struct ymmh_struct ymmh;
};

typedef struct raw_spinlock {
 arch_spinlock_t raw_lock;
} raw_spinlock_t;

struct cgroup_subsys_state {
 struct cgroup *cgroup;
 struct cgroup_subsys *ss;
 struct percpu_ref refcnt;
 struct cgroup_subsys_state *parent;
 unsigned long flags;
 struct css_id *id;
 struct callback_head callback_head;
 struct work_struct destroy_work;
};

struct class_attribute {
 struct attribute attr;
 ssize_t (*show)(struct class *class, struct class_attribute *attr,
   char *buf);
 ssize_t (*store)(struct class *class, struct class_attribute *attr,
   const char *buf, size_t count);
};

struct compat_robust_list_head {
 struct compat_robust_list list;
 compat_long_t futex_offset;
 compat_uptr_t list_op_pending;
};

struct delayed_work {
 struct work_struct work;
 struct timer_list timer;
 struct workqueue_struct *wq;
 int cpu;
};

struct device_attribute {
 struct attribute attr;
 ssize_t (*show)(struct device *dev, struct device_attribute *attr,
   char *buf);
 ssize_t (*store)(struct device *dev, struct device_attribute *attr,
    const char *buf, size_t count);
};

struct dir_context {
 const filldir_t actor;
 loff_t pos;
};

union ethtool_flow_union {
 struct ethtool_tcpip4_spec tcp_ip4_spec;
 struct ethtool_tcpip4_spec udp_ip4_spec;
 struct ethtool_tcpip4_spec sctp_ip4_spec;
 struct ethtool_ah_espip4_spec ah_ip4_spec;
 struct ethtool_ah_espip4_spec esp_ip4_spec;
 struct ethtool_usrip4_spec usr_ip4_spec;
 struct ethhdr ether_spec;
 __u8 hdata[52];
};

struct group_info {
 atomic_t usage;
 int ngroups;
 int nblocks;
 kgid_t small_block[32];
 kgid_t *blocks[0];
};

struct i387_soft_struct {
 u32 cwd;
 u32 swd;
 u32 twd;
 u32 fip;
 u32 fcs;
 u32 foo;
 u32 fos;
 u32 st_space[20];
 u8 ftop;
 u8 changed;
 u8 lookahead;
 u8 no_update;
 u8 rm;
 u8 alimit;
 struct math_emu_info *info;
 u32 entry_eip;
};

struct ifreq {
 union
 {
  char ifrn_name[16];
 } ifr_ifrn;
 union {
  struct sockaddr ifru_addr;
  struct sockaddr ifru_dstaddr;
  struct sockaddr ifru_broadaddr;
  struct sockaddr ifru_netmask;
  struct sockaddr ifru_hwaddr;
  short ifru_flags;
  int ifru_ivalue;
  int ifru_mtu;
  struct ifmap ifru_map;
  char ifru_slave[16];
  char ifru_newname[16];
  void * ifru_data;
  struct if_settings ifru_settings;
 } ifr_ifru;
};

struct inetpeer_addr {
 struct inetpeer_addr_base addr;
 __u16 family;
};

struct ip6_sf_list {
 struct ip6_sf_list *sf_next;
 struct in6_addr sf_addr;
 unsigned long sf_count[2];
 unsigned char sf_gsresp;
 unsigned char sf_oldin;
 unsigned char sf_crcount;
};

struct ipv6_devstat {
 struct proc_dir_entry *proc_dir_entry;
 __typeof__(struct ipstats_mib) *ipv6[1];
 __typeof__(struct icmpv6_mib_device) *icmpv6dev;
 __typeof__(struct icmpv6msg_mib_device) *icmpv6msgdev;
};

struct k_sigaction {
 struct sigaction sa;
};

struct kmem_cache {
 struct kmem_cache_cpu *cpu_slab;
 unsigned long flags;
 unsigned long min_partial;
 int size;
 int object_size;
 int offset;
 int cpu_partial;
 struct kmem_cache_order_objects oo;
 struct kmem_cache_order_objects max;
 struct kmem_cache_order_objects min;
 gfp_t allocflags;
 atomic_t refcount;
 void (*ctor)(void *);
 int inuse;
 int align;
 int reserved;
 const char *name;
 struct list_head list;
 struct kobject kobj;
 int remote_node_defrag_ratio;
 struct kmem_cache_node *node[(1 << CONFIG_NODES_SHIFT)];
};

struct kqid {
 union {
  kuid_t uid;
  kgid_t gid;
  kprojid_t projid;
 };
 enum quota_type type;
};

struct kstat {
 u64 ino;
 dev_t dev;
 umode_t mode;
 unsigned int nlink;
 kuid_t uid;
 kgid_t gid;
 dev_t rdev;
 loff_t size;
 struct timespec atime;
 struct timespec mtime;
 struct timespec ctime;
 unsigned long blksize;
 unsigned long long blocks;
};

struct mem_dqblk {
 qsize_t dqb_bhardlimit;
 qsize_t dqb_bsoftlimit;
 qsize_t dqb_curspace;
 qsize_t dqb_rsvspace;
 qsize_t dqb_ihardlimit;
 qsize_t dqb_isoftlimit;
 qsize_t dqb_curinodes;
 time_t dqb_btime;
 time_t dqb_itime;
};

struct msghdr {
 void * msg_name;
 int msg_namelen;
 struct iovec * msg_iov;
 __kernel_size_t msg_iovlen;
 void * msg_control;
 __kernel_size_t msg_controllen;
 unsigned int msg_flags;
};

struct netdev_rx_queue {
 struct rps_map *rps_map;
 struct rps_dev_flow_table *rps_flow_table;
 struct kobject kobj;
 struct net_device *dev;
};

struct netns_mib {
 __typeof__(struct tcp_mib) *tcp_statistics[1];
 __typeof__(struct ipstats_mib) *ip_statistics[1];
 __typeof__(struct linux_mib) *net_statistics[1];
 __typeof__(struct udp_mib) *udp_statistics[1];
 __typeof__(struct udp_mib) *udplite_statistics[1];
 __typeof__(struct icmp_mib) *icmp_statistics[1];
 __typeof__(struct icmpmsg_mib) *icmpmsg_statistics;
 struct proc_dir_entry *proc_net_devsnmp6;
 __typeof__(struct udp_mib) *udp_stats_in6[1];
 __typeof__(struct udp_mib) *udplite_stats_in6[1];
 __typeof__(struct ipstats_mib) *ipv6_statistics[1];
 __typeof__(struct icmpv6_mib) *icmpv6_statistics[1];
 __typeof__(struct icmpv6msg_mib) *icmpv6msg_statistics;
};

struct posix_acl_entry {
 short e_tag;
 unsigned short e_perm;
 union {
  kuid_t e_uid;
  kgid_t e_gid;
  unsigned int e_id;
 };
};

struct restart_block {
 long (*fn)(struct restart_block *);
 union {
  struct {
   u32 *uaddr;
   u32 val;
   u32 flags;
   u32 bitset;
   u64 time;
   u32 *uaddr2;
  } futex;
  struct {
   clockid_t clockid;
   struct timespec *rmtp;
   struct compat_timespec *compat_rmtp;
   u64 expires;
  } nanosleep;
  struct {
   struct pollfd *ufds;
   int nfds;
   int has_timeout;
   unsigned long tv_sec;
   unsigned long tv_nsec;
  } poll;
 };
};

struct sg_table {
 struct scatterlist *sgl;
 unsigned int nents;
 unsigned int orig_nents;
};

struct shrinker {
 unsigned long (*count_objects)(struct shrinker *,
           struct shrink_control *sc);
 unsigned long (*scan_objects)(struct shrinker *,
          struct shrink_control *sc);
 int seeks;
 long batch;
 unsigned long flags;
 struct list_head list;
 atomic_long_t *nr_deferred;
};

struct sk_buff {
 struct sk_buff *next;
 struct sk_buff *prev;
 ktime_t tstamp;
 struct sock *sk;
 struct net_device *dev;
 char cb[48] ;
 unsigned long _skb_refdst;
 struct sec_path *sp;
 unsigned int len,
    data_len;
 __u16 mac_len,
    hdr_len;
 union {
  __wsum csum;
  struct {
   __u16 csum_start;
   __u16 csum_offset;
  };
 };
 __u32 priority;
 ;
 __u8 local_df:1,
    cloned:1,
    ip_summed:2,
    nohdr:1,
    nfctinfo:3;
 __u8 pkt_type:3,
    fclone:2,
    ipvs_property:1,
    peeked:1,
    nf_trace:1;
 ;
 __be16 protocol;
 void (*destructor)(struct sk_buff *skb);
 struct nf_conntrack *nfct;
 int skb_iif;
 __u32 rxhash;
 __be16 vlan_proto;
 __u16 vlan_tci;
 __u16 tc_index;
 __u16 tc_verd;
 __u16 queue_mapping;
 ;
 __u8 ndisc_nodetype:2;
 __u8 pfmemalloc:1;
 __u8 ooo_okay:1;
 __u8 l4_rxhash:1;
 __u8 wifi_acked_valid:1;
 __u8 wifi_acked:1;
 __u8 no_fcs:1;
 __u8 head_frag:1;
 __u8 encapsulation:1;
 ;
 union {
  unsigned int napi_id;
  dma_cookie_t dma_cookie;
 };
 __u32 secmark;
 union {
  __u32 mark;
  __u32 dropcount;
  __u32 reserved_tailroom;
 };
 __be16 inner_protocol;
 __u16 inner_transport_header;
 __u16 inner_network_header;
 __u16 inner_mac_header;
 __u16 transport_header;
 __u16 network_header;
 __u16 mac_header;
 sk_buff_data_t tail;
 sk_buff_data_t end;
 unsigned char *head,
    *data;
 unsigned int truesize;
 atomic_t users;
};

struct sysfs_ops {
 ssize_t (*show)(struct kobject *, struct attribute *, char *);
 ssize_t (*store)(struct kobject *, struct attribute *, const char *, size_t);
};

struct timerqueue_node {
 struct rb_node node;
 ktime_t expires;
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

typedef rx_handler_result_t rx_handler_func_t(struct sk_buff **pskb);

typedef struct spinlock {
 union {
  struct raw_spinlock rlock;
 };
} spinlock_t;

struct css_set {
 atomic_t refcount;
 struct hlist_node hlist;
 struct list_head tasks;
 struct list_head cgrp_links;
 struct cgroup_subsys_state *subsys[CGROUP_SUBSYS_COUNT];
 struct callback_head callback_head;
};

struct dst_entry {
 struct callback_head callback_head;
 struct dst_entry *child;
 struct net_device *dev;
 struct dst_ops *ops;
 unsigned long _metrics;
 unsigned long expires;
 struct dst_entry *path;
 struct dst_entry *from;
 struct xfrm_state *xfrm;
 int (*input)(struct sk_buff *);
 int (*output)(struct sk_buff *);
 unsigned short flags;
 unsigned short pending_confirm;
 short error;
 short obsolete;
 unsigned short header_len;
 unsigned short trailer_len;
 __u32 __pad2;
 long __pad_to_align_refcnt[2];
 atomic_t __refcnt;
 int __use;
 unsigned long lastuse;
 union {
  struct dst_entry *next;
  struct rtable *rt_next;
  struct rt6_info *rt6_next;
  struct dn_route *dn_next;
 };
};

struct ethtool_rx_flow_spec {
 __u32 flow_type;
 union ethtool_flow_union h_u;
 struct ethtool_flow_ext h_ext;
 union ethtool_flow_union m_u;
 struct ethtool_flow_ext m_ext;
 __u64 ring_cookie;
 __u32 location;
};

struct inet_peer {
 struct inet_peer *avl_left, *avl_right;
 struct inetpeer_addr daddr;
 __u32 avl_height;
 u32 metrics[(__RTAX_MAX - 1)];
 u32 rate_tokens;
 unsigned long rate_last;
 union {
  struct list_head gc_list;
  struct callback_head gc_rcu;
 };
 union {
  struct {
   atomic_unchecked_t rid;
   atomic_unchecked_t ip_id_count;
  };
  struct callback_head rcu;
  struct inet_peer *gc_next;
 };
 __u32 dtime;
 atomic_t refcnt;
};

struct kobj_type {
 void (*release)(struct kobject *kobj);
 const struct sysfs_ops *sysfs_ops;
 struct attribute **default_attrs;
 const struct kobj_ns_type_operations *(*child_ns_type)(struct kobject *kobj);
 const void *(*namespace)(struct kobject *kobj);
};

struct neigh_ops {
 int family;
 void (*solicit)(struct neighbour *, struct sk_buff *);
 void (*error_report)(struct neighbour *, struct sk_buff *);
 int (*output)(struct neighbour *, struct sk_buff *);
 int (*connected_output)(struct neighbour *, struct sk_buff *);
};

struct percpu_counter {
 raw_spinlock_t lock;
 s64 count;
 struct list_head list;
 s32 *counters;
};

struct pm_qos_request {
 struct plist_node node;
 int pm_qos_class;
 struct delayed_work work;
};

struct posix_acl {
 union {
  atomic_t a_refcount;
  struct callback_head a_rcu;
 };
 unsigned int a_count;
 struct posix_acl_entry a_entries[0];
};

struct quotactl_ops {
 int (*quota_on)(struct super_block *, int, int, struct path *);
 int (*quota_on_meta)(struct super_block *, int, int);
 int (*quota_off)(struct super_block *, int);
 int (*quota_sync)(struct super_block *, int);
 int (*get_info)(struct super_block *, int, struct if_dqinfo *);
 int (*set_info)(struct super_block *, int, struct if_dqinfo *);
 int (*get_dqblk)(struct super_block *, struct kqid, struct fs_disk_quota *);
 int (*set_dqblk)(struct super_block *, struct kqid, struct fs_disk_quota *);
 int (*get_xstate)(struct super_block *, struct fs_quota_stat *);
 int (*set_xstate)(struct super_block *, unsigned int, int);
 int (*get_xstatev)(struct super_block *, struct fs_quota_statv *);
};

struct request_sock_ops {
 int family;
 int obj_size;
 struct kmem_cache *slab;
 char *slab_name;
 int (*rtx_syn_ack)(struct sock *sk,
           struct request_sock *req);
 void (*send_ack)(struct sock *sk, struct sk_buff *skb,
        struct request_sock *req);
 void (*send_reset)(struct sock *sk,
          struct sk_buff *skb);
 void (*destructor)(struct request_sock *req);
 void (*syn_ack_timeout)(struct sock *sk,
        struct request_sock *req);
};

struct rw_semaphore {
 long count;
 raw_spinlock_t wait_lock;
 struct list_head wait_list;
};

struct sk_filter
{
 atomic_t refcnt;
 unsigned int len;
 struct callback_head rcu;
 unsigned int (*bpf_func)(const struct sk_buff *skb,
         const struct sock_filter *filter);
 union {
  struct sock_filter insns[0];
  struct work_struct work;
 };
};

struct thread_group_cputimer {
 struct task_cputime cputime;
 int running;
 raw_spinlock_t lock;
};

union thread_xstate {
 struct i387_fsave_struct fsave;
 struct i387_fxsave_struct fxsave;
 struct i387_soft_struct soft;
 struct xsave_struct xsave;
};

struct timerqueue_head {
 struct rb_root head;
 struct timerqueue_node *next;
};

struct timewait_sock_ops {
 struct kmem_cache *twsk_slab;
 char *twsk_slab_name;
 unsigned int twsk_obj_size;
 int (*twsk_unique)(struct sock *sk,
           struct sock *sktw, void *twp);
 void (*twsk_destructor)(struct sock *sk);
};

struct uts_namespace {
 struct kref kref;
 struct new_utsname name;
 struct user_namespace *user_ns;
 unsigned int proc_inum;
};

typedef struct {
 struct seqcount seqcount;
 spinlock_t lock;
} seqlock_t;

struct __wait_queue_head {
 spinlock_t lock;
 struct list_head task_list;
};

struct blocking_notifier_head {
 struct rw_semaphore rwsem;
 struct notifier_block *head;
};

struct ethtool_rxnfc {
 __u32 cmd;
 __u32 flow_type;
 __u64 data;
 struct ethtool_rx_flow_spec fs;
 __u32 rule_cnt;
 __u32 rule_locs[0];
};

struct fpu {
 unsigned int last_cpu;
 unsigned int has_fpu;
 union thread_xstate *state;
};

struct fs_struct {
 atomic_t users;
 spinlock_t lock;
 seqcount_t seq;
 int umask;
 int in_exec;
 struct path root, pwd;
};

struct hrtimer_clock_base {
 struct hrtimer_cpu_base *cpu_base;
 int index;
 clockid_t clockid;
 struct timerqueue_head active;
 ktime_t resolution;
 ktime_t (*get_time)(void);
 ktime_t softirq_time;
 ktime_t offset;
};

struct idr {
 struct idr_layer *hint;
 struct idr_layer *top;
 struct idr_layer *id_free;
 int layers;
 int id_free_cnt;
 int cur;
 spinlock_t lock;
};

struct ifacaddr6 {
 struct in6_addr aca_addr;
 struct inet6_dev *aca_idev;
 struct rt6_info *aca_rt;
 struct ifacaddr6 *aca_next;
 int aca_users;
 atomic_t aca_refcnt;
 spinlock_t aca_lock;
 unsigned long aca_cstamp;
 unsigned long aca_tstamp;
};

struct ifmcaddr6 {
 struct in6_addr mca_addr;
 struct inet6_dev *idev;
 struct ifmcaddr6 *next;
 struct ip6_sf_list *mca_sources;
 struct ip6_sf_list *mca_tomb;
 unsigned int mca_sfmode;
 unsigned char mca_crcount;
 unsigned long mca_sfcount[2];
 struct timer_list mca_timer;
 unsigned int mca_flags;
 int mca_users;
 atomic_t mca_refcnt;
 spinlock_t mca_lock;
 unsigned long mca_cstamp;
 unsigned long mca_tstamp;
};

struct inet_bind_hashbucket {
 spinlock_t lock;
 struct hlist_head chain;
};

struct inet_listen_hashbucket {
 spinlock_t lock;
 struct hlist_nulls_head head;
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

struct kset {
 struct list_head list;
 spinlock_t list_lock;
 struct kobject kobj;
 const struct kset_uevent_ops *uevent_ops;
};

struct list_lru_node {
 spinlock_t lock;
 struct list_head list;
 long nr_items;
};

struct lockref {
 union {
  __u64  lock_count;
  struct {
   spinlock_t lock;
   unsigned int count;
  };
 };
};

struct mutex {
 atomic_t count;
 spinlock_t wait_lock;
 struct list_head wait_list;
 struct task_struct *owner;
 void *spin_mlock;
};

struct napi_struct {
 struct list_head poll_list;
 unsigned long state;
 int weight;
 unsigned int gro_count;
 int (*poll)(struct napi_struct *, int);
 spinlock_t poll_lock;
 int poll_owner;
 struct net_device *dev;
 struct sk_buff *gro_list;
 struct sk_buff *skb;
 struct list_head dev_list;
 struct hlist_node napi_hash_node;
 unsigned int napi_id;
};

struct netdev_queue {
 struct net_device *dev;
 struct Qdisc *qdisc;
 struct Qdisc *qdisc_sleeping;
 struct kobject kobj;
 int numa_node;
 spinlock_t _xmit_lock ;
 int xmit_lock_owner;
 unsigned long trans_start;
 unsigned long trans_timeout;
 unsigned long state;
 struct dql dql;
};

struct netns_frags {
 int nqueues;
 struct list_head lru_list;
 spinlock_t lru_lock;
 struct percpu_counter mem ;
 int timeout;
 int high_thresh;
 int low_thresh;
};

struct page {
 unsigned long flags;
 union {
  struct address_space *mapping;
  void *s_mem;
 };
 struct {
  union {
   unsigned long index;
   void *freelist;
   bool pfmemalloc;
  };
  union {
   unsigned long counters;
   struct {
    union {
     atomic_t _mapcount;
     struct {
      unsigned inuse:16;
      unsigned objects:15;
      unsigned frozen:1;
     };
     int units;
    };
    atomic_t _count;
   };
   unsigned int active;
  };
 };
 union {
  struct list_head lru;
  struct {
   struct page *next;
   int pages;
   int pobjects;
  };
  struct list_head list;
  struct slab *slab_page;
  struct callback_head callback_head;
 };
 union {
  unsigned long private;
  spinlock_t ptl;
  struct kmem_cache *slab_cache;
  struct page *first_page;
 };
};

struct pm_subsys_data {
 spinlock_t lock;
 unsigned int refcount;
};

struct res_counter {
 unsigned long long usage;
 unsigned long long max_usage;
 unsigned long long limit;
 unsigned long long soft_limit;
 unsigned long long failcnt;
 spinlock_t lock;
 struct res_counter *parent;
};

struct rtable {
 struct dst_entry dst;
 int rt_genid;
 unsigned int rt_flags;
 __u16 rt_type;
 __u8 rt_is_input;
 __u8 rt_uses_gateway;
 int rt_iif;
 __be32 rt_gateway;
 u32 rt_pmtu;
 struct list_head rt_uncached;
};

struct simple_xattrs {
 struct list_head head;
 spinlock_t lock;
};

struct sk_buff_head {
 struct sk_buff *next;
 struct sk_buff *prev;
 __u32 qlen;
 spinlock_t lock;
};

struct task_delay_info {
 spinlock_t lock;
 unsigned int flags;
 struct timespec blkio_start, blkio_end;
 u64 blkio_delay;
 u64 swapin_delay;
 u32 blkio_count;
 u32 swapin_count;
 struct timespec freepages_start, freepages_end;
 u64 freepages_delay;
 u32 freepages_count;
};

struct wakeup_source {
 const char *name;
 struct list_head entry;
 spinlock_t lock;
 struct timer_list timer;
 unsigned long timer_expires;
 ktime_t total_time;
 ktime_t max_time;
 ktime_t last_time;
 ktime_t start_prevent_time;
 ktime_t prevent_sleep_time;
 unsigned long event_count;
 unsigned long active_count;
 unsigned long relax_count;
 unsigned long expire_count;
 unsigned long wakeup_count;
 bool active:1;
 bool autosleep_enabled:1;
};

typedef struct {
 struct desc_struct *ldt;
 int size;
 unsigned short ia32_compat;
 struct mutex lock;
 unsigned long vdso;
} mm_context_t;

typedef struct __wait_queue_head wait_queue_head_t;

struct block_device {
 dev_t bd_dev;
 int bd_openers;
 struct inode * bd_inode;
 struct super_block * bd_super;
 struct mutex bd_mutex;
 struct list_head bd_inodes;
 void * bd_claiming;
 void * bd_holder;
 int bd_holders;
 bool bd_write_holder;
 struct list_head bd_holder_disks;
 struct block_device * bd_contains;
 unsigned bd_block_size;
 struct hd_struct * bd_part;
 unsigned bd_part_count;
 int bd_invalidated;
 struct gendisk * bd_disk;
 struct request_queue * bd_queue;
 struct list_head bd_list;
 unsigned long bd_private;
 int bd_fsfreeze_count;
 struct mutex bd_fsfreeze_mutex;
};

struct cg_proto {
 struct res_counter memory_allocated;
 struct percpu_counter sockets_allocated;
 int memory_pressure;
 long sysctl_mem[3];
 unsigned long flags;
 struct mem_cgroup *memcg;
};

struct dentry {
 unsigned int d_flags;
 seqcount_t d_seq;
 struct hlist_bl_node d_hash;
 struct dentry *d_parent;
 struct qstr d_name;
 struct inode *d_inode;
 unsigned char d_iname[32];
 struct lockref d_lockref;
 const struct dentry_operations *d_op;
 struct super_block *d_sb;
 unsigned long d_time;
 void *d_fsdata;
 struct list_head d_lru;
 union {
  struct list_head d_child;
   struct callback_head d_rcu;
 } d_u;
 struct list_head d_subdirs;
 struct hlist_node d_alias;
};

struct ethtool_ops {
 int (*get_settings)(struct net_device *, struct ethtool_cmd *);
 int (*set_settings)(struct net_device *, struct ethtool_cmd *);
 void (*get_drvinfo)(struct net_device *, struct ethtool_drvinfo *);
 int (*get_regs_len)(struct net_device *);
 void (*get_regs)(struct net_device *, struct ethtool_regs *, void *);
 void (*get_wol)(struct net_device *, struct ethtool_wolinfo *);
 int (*set_wol)(struct net_device *, struct ethtool_wolinfo *);
 u32 (*get_msglevel)(struct net_device *);
 void (*set_msglevel)(struct net_device *, u32);
 int (*nway_reset)(struct net_device *);
 u32 (*get_link)(struct net_device *);
 int (*get_eeprom_len)(struct net_device *);
 int (*get_eeprom)(struct net_device *,
         struct ethtool_eeprom *, u8 *);
 int (*set_eeprom)(struct net_device *,
         struct ethtool_eeprom *, u8 *);
 int (*get_coalesce)(struct net_device *, struct ethtool_coalesce *);
 int (*set_coalesce)(struct net_device *, struct ethtool_coalesce *);
 void (*get_ringparam)(struct net_device *,
     struct ethtool_ringparam *);
 int (*set_ringparam)(struct net_device *,
     struct ethtool_ringparam *);
 void (*get_pauseparam)(struct net_device *,
      struct ethtool_pauseparam*);
 int (*set_pauseparam)(struct net_device *,
      struct ethtool_pauseparam*);
 void (*self_test)(struct net_device *, struct ethtool_test *, u64 *);
 void (*get_strings)(struct net_device *, u32 stringset, u8 *);
 int (*set_phys_id)(struct net_device *, enum ethtool_phys_id_state);
 void (*get_ethtool_stats)(struct net_device *,
         struct ethtool_stats *, u64 *);
 int (*begin)(struct net_device *);
 void (*complete)(struct net_device *);
 u32 (*get_priv_flags)(struct net_device *);
 int (*set_priv_flags)(struct net_device *, u32);
 int (*get_sset_count)(struct net_device *, int);
 int (*get_rxnfc)(struct net_device *,
        struct ethtool_rxnfc *, u32 *rule_locs);
 int (*set_rxnfc)(struct net_device *, struct ethtool_rxnfc *);
 int (*flash_device)(struct net_device *, struct ethtool_flash *);
 int (*reset)(struct net_device *, u32 *);
 u32 (*get_rxfh_indir_size)(struct net_device *);
 int (*get_rxfh_indir)(struct net_device *, u32 *);
 int (*set_rxfh_indir)(struct net_device *, const u32 *);
 void (*get_channels)(struct net_device *, struct ethtool_channels *);
 int (*set_channels)(struct net_device *, struct ethtool_channels *);
 int (*get_dump_flag)(struct net_device *, struct ethtool_dump *);
 int (*get_dump_data)(struct net_device *,
     struct ethtool_dump *, void *);
 int (*set_dump)(struct net_device *, struct ethtool_dump *);
 int (*get_ts_info)(struct net_device *, struct ethtool_ts_info *);
 int (*get_module_info)(struct net_device *,
       struct ethtool_modinfo *);
 int (*get_module_eeprom)(struct net_device *,
         struct ethtool_eeprom *, u8 *);
 int (*get_eee)(struct net_device *, struct ethtool_eee *);
 int (*set_eee)(struct net_device *, struct ethtool_eee *);
};

struct hh_cache {
 u16 hh_len;
 u16 __pad;
 seqlock_t hh_lock;
 unsigned long hh_data[(((96)+(16 -1))&~(16 - 1)) / sizeof(long)];
};

struct hrtimer {
 struct timerqueue_node node;
 ktime_t _softexpires;
 enum hrtimer_restart (*function)(struct hrtimer *);
 struct hrtimer_clock_base *base;
 unsigned long state;
 int start_pid;
 void *start_site;
 char start_comm[16];
};

struct hrtimer_cpu_base {
 raw_spinlock_t lock;
 unsigned int active_bases;
 unsigned int clock_was_set;
 ktime_t expires_next;
 int hres_active;
 int hang_detected;
 unsigned long nr_events;
 unsigned long nr_retries;
 unsigned long nr_hangs;
 ktime_t max_hang_time;
 struct hrtimer_clock_base clock_base[HRTIMER_MAX_CLOCK_BASES];
};

struct inet_hashinfo {
 struct inet_ehash_bucket *ehash;
 spinlock_t *ehash_locks;
 unsigned int ehash_mask;
 unsigned int ehash_locks_mask;
 struct inet_bind_hashbucket *bhash;
 unsigned int bhash_size;
 struct kmem_cache *bind_bucket_cachep;
 struct inet_listen_hashbucket listening_hash[32]
     ;
 atomic_t bsockets;
};

struct inet_peer_base {
 struct inet_peer *root;
 seqlock_t lock;
 u32 flush_seq;
 int total;
};

struct list_lru {
 struct list_lru_node *node;
 nodemask_t active_nodes;
};

struct local_ports {
 seqlock_t lock;
 int range[2];
};

struct netns_packet {
 struct mutex sklist_lock;
 struct hlist_head sklist;
};

struct page_frag {
 struct page *page;
 __u32 offset;
 __u32 size;
};

struct pipe_buffer {
 struct page *page;
 unsigned int offset, len;
 const struct pipe_buf_operations *ops;
 unsigned int flags;
 unsigned long private;
};

struct pm_qos_constraints {
 struct plist_head list;
 s32 target_value;
 s32 default_value;
 enum pm_qos_type type;
 struct blocking_notifier_head *notifiers;
};

struct seq_file {
 char *buf;
 size_t size;
 size_t from;
 size_t count;
 size_t pad_until;
 loff_t index;
 loff_t read_pos;
 u64 version;
 struct mutex lock;
 const struct seq_operations *op;
 int poll_event;
 void *private;
};

struct thread_struct {
 struct desc_struct tls_array[3];
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
 struct perf_event *ptrace_bps[4];
 unsigned long debugreg6;
 unsigned long ptrace_dr7;
 unsigned long cr2;
 unsigned long trap_nr;
 unsigned long error_code;
 struct fpu fpu;
 unsigned long *io_bitmap_ptr;
 unsigned long iopl;
 unsigned io_bitmap_max;
 unsigned char fpu_counter;
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

struct vm_fault {
 unsigned int flags;
 unsigned long pgoff;
 void *virtual_address;
 struct page *page;
};

typedef struct {
 spinlock_t slock;
 int owned;
 wait_queue_head_t wq;
} socket_lock_t;

struct cgroup {
 unsigned long flags;
 int id;
 int nr_css;
 struct list_head sibling;
 struct list_head children;
 struct list_head files;
 struct cgroup *parent;
 struct dentry *dentry;
 u64 serial_nr;
 struct cgroup_name *name;
 struct cgroup_subsys_state *subsys[CGROUP_SUBSYS_COUNT];
 struct cgroupfs_root *root;
 struct list_head cset_links;
 struct list_head release_list;
 struct list_head pidlists;
 struct mutex pidlist_mutex;
 struct cgroup_subsys_state dummy_css;
 struct callback_head callback_head;
 struct work_struct destroy_work;
 struct list_head event_list;
 spinlock_t event_list_lock;
 struct simple_xattrs xattrs;
};

struct completion {
 unsigned int done;
 wait_queue_head_t wait;
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

struct ctl_table_poll {
 atomic_t event;
 wait_queue_head_t wait;
};

struct dev_pm_qos {
 struct pm_qos_constraints latency;
 struct pm_qos_flags flags;
 struct dev_pm_qos_request *latency_req;
 struct dev_pm_qos_request *flags_req;
};

struct dquot {
 struct hlist_node dq_hash;
 struct list_head dq_inuse;
 struct list_head dq_free;
 struct list_head dq_dirty;
 struct mutex dq_lock;
 atomic_t dq_count;
 wait_queue_head_t dq_wait_unused;
 struct super_block *dq_sb;
 struct kqid dq_id;
 loff_t dq_off;
 unsigned long dq_flags;
 struct mem_dqblk dq_dqb;
};

struct neighbour {
 struct neighbour *next;
 struct neigh_table *tbl;
 struct neigh_parms *parms;
 unsigned long confirmed;
 unsigned long updated;
 rwlock_t lock;
 atomic_t refcnt;
 struct sk_buff_head arp_queue;
 unsigned int arp_queue_len_bytes;
 struct timer_list timer;
 unsigned long used;
 atomic_t probes;
 __u8 flags;
 __u8 nud_state;
 __u8 type;
 __u8 dead;
 seqlock_t ha_lock;
 unsigned char ha[((((32)) + ((typeof((32)))((sizeof(unsigned long))) - 1)) & ~((typeof((32)))((sizeof(unsigned long))) - 1))];
 struct hh_cache hh;
 int (*output)(struct neighbour *, struct sk_buff *);
 const struct neigh_ops *ops;
 struct callback_head rcu;
 struct net_device *dev;
 u8 primary_key[0];
};

struct pid_namespace {
 struct kref kref;
 struct pidmap pidmap[(((CONFIG_BASE_SMALL ? ((1UL) << 12) * 8 : (sizeof(long) > 4 ? 4 * 1024 * 1024 : (CONFIG_BASE_SMALL ? 0x1000 : 0x8000)))+(((1UL) << 12) * 8)-1)/(((1UL) << 12) * 8))];
 struct callback_head rcu;
 int last_pid;
 unsigned int nr_hashed;
 struct task_struct *child_reaper;
 struct kmem_cache *pid_cachep;
 unsigned int level;
 struct pid_namespace *parent;
 struct vfsmount *proc_mnt;
 struct dentry *proc_self;
 struct bsd_acct_struct *bacct;
 struct user_namespace *user_ns;
 struct work_struct proc_work;
 kgid_t pid_gid;
 int hide_pid;
 int reboot;
 unsigned int proc_inum;
};

struct sb_writers {
 struct percpu_counter counter[(SB_FREEZE_COMPLETE - 1)];
 wait_queue_head_t wait;
 int frozen;
 wait_queue_head_t wait_unfrozen;
};

struct sighand_struct {
 atomic_t count;
 struct k_sigaction action[64];
 spinlock_t siglock;
 wait_queue_head_t signalfd_wqh;
};

struct vm_operations_struct {
 void (*open)(struct vm_area_struct * area);
 void (*close)(struct vm_area_struct * area);
 int (*fault)(struct vm_area_struct *vma, struct vm_fault *vmf);
 int (*page_mkwrite)(struct vm_area_struct *vma, struct vm_fault *vmf);
 ssize_t (*access)(struct vm_area_struct *vma, unsigned long addr,
        void *buf, size_t len, int write);
 int (*set_policy)(struct vm_area_struct *vma, struct mempolicy *new);
 struct mempolicy *(*get_policy)(struct vm_area_struct *vma,
     unsigned long addr);
 int (*migrate)(struct vm_area_struct *vma, const nodemask_t *from,
  const nodemask_t *to, unsigned long flags);
 int (*remap_pages)(struct vm_area_struct *vma, unsigned long addr,
      unsigned long size, unsigned long pgoff);
};

struct xattr_handler {
 const char *prefix;
 int flags;
 size_t (*list)(struct dentry *dentry, char *list, size_t list_size,
         const char *name, size_t name_len, int handler_flags);
 int (*get)(struct dentry *dentry, const char *name, void *buffer,
     size_t size, int handler_flags);
 int (*set)(struct dentry *dentry, const char *name, const void *buffer,
     size_t size, int flags, int handler_flags);
};

struct ctl_table
{
 const char *procname;
 void *data;
 int maxlen;
 umode_t mode;
 struct ctl_table *child;
 proc_handler *proc_handler;
 struct ctl_table_poll *poll;
 void *extra1;
 void *extra2;
};

struct dev_pm_info {
 pm_message_t power_state;
 unsigned int can_wakeup:1;
 unsigned int async_suspend:1;
 bool is_prepared:1;
 bool is_suspended:1;
 bool ignore_children:1;
 bool early_init:1;
 spinlock_t lock;
 struct list_head entry;
 struct completion completion;
 struct wakeup_source *wakeup;
 bool wakeup_path:1;
 bool syscore:1;
 struct pm_subsys_data *subsys_data;
 struct dev_pm_qos *qos;
};

struct header_ops {
 int (*create) (struct sk_buff *skb, struct net_device *dev,
      unsigned short type, const void *daddr,
      const void *saddr, unsigned int len);
 int (*parse)(const struct sk_buff *skb, unsigned char *haddr);
 int (*rebuild)(struct sk_buff *skb);
 int (*cache)(const struct neighbour *neigh, struct hh_cache *hh, __be16 type);
 void (*cache_update)(struct hh_cache *hh,
    const struct net_device *dev,
    const unsigned char *haddr);
};

struct module_kobject {
 struct kobject kobj;
 struct module *mod;
 struct kobject *drivers_dir;
 struct module_param_attrs *mp;
 struct completion *kobj_completion;
};

struct neigh_hash_table {
 struct neighbour **hash_buckets;
 unsigned int hash_shift;
 __u32 hash_rnd[4];
 struct callback_head rcu;
};

struct neigh_parms {
 struct net *net;
 struct net_device *dev;
 struct neigh_parms *next;
 int (*neigh_setup)(struct neighbour *);
 void (*neigh_cleanup)(struct neighbour *);
 struct neigh_table *tbl;
 void *sysctl_table;
 int dead;
 atomic_t refcnt;
 struct callback_head callback_head;
 int base_reachable_time;
 int retrans_time;
 int gc_staletime;
 int reachable_time;
 int delay_probe_time;
 int queue_len_bytes;
 int ucast_probes;
 int app_probes;
 int mcast_probes;
 int anycast_delay;
 int proxy_delay;
 int proxy_qlen;
 int locktime;
};

struct nsproxy {
 atomic_t count;
 struct uts_namespace *uts_ns;
 struct ipc_namespace *ipc_ns;
 struct mnt_namespace *mnt_ns;
 struct pid_namespace *pid_ns_for_children;
 struct net *net_ns;
};

struct quota_format_ops {
 int (*check_quota_file)(struct super_block *sb, int type);
 int (*read_file_info)(struct super_block *sb, int type);
 int (*write_file_info)(struct super_block *sb, int type);
 int (*free_file_info)(struct super_block *sb, int type);
 int (*read_dqblk)(struct dquot *dquot);
 int (*commit_dqblk)(struct dquot *dquot);
 int (*release_dqblk)(struct dquot *dquot);
};

struct upid {
 int nr;
 struct pid_namespace *ns;
 struct hlist_node pid_chain;
};

typedef struct ctl_table ctl_table_no_const;

struct ctl_table_header
{
 union {
  struct {
   struct ctl_table *ctl_table;
   int used;
   int count;
   int nreg;
  };
  struct callback_head rcu;
 };
 struct completion *unregistering;
 struct ctl_table *ctl_table_arg;
 struct ctl_table_root *root;
 struct ctl_table_set *set;
 struct ctl_dir *parent;
 struct ctl_node *node;
};

struct inet6_dev {
 struct net_device *dev;
 struct list_head addr_list;
 struct ifmcaddr6 *mc_list;
 struct ifmcaddr6 *mc_tomb;
 spinlock_t mc_lock;
 unsigned char mc_qrv;
 unsigned char mc_gq_running;
 unsigned char mc_ifc_count;
 unsigned char mc_dad_count;
 unsigned long mc_v1_seen;
 unsigned long mc_qi;
 unsigned long mc_qri;
 unsigned long mc_maxdelay;
 struct timer_list mc_gq_timer;
 struct timer_list mc_ifc_timer;
 struct timer_list mc_dad_timer;
 struct ifacaddr6 *ac_list;
 rwlock_t lock;
 atomic_t refcnt;
 __u32 if_flags;
 int dead;
 u8 rndid[8];
 struct timer_list regen_timer;
 struct list_head tempaddr_list;
 struct in6_addr token;
 struct neigh_parms *nd_parms;
 struct ipv6_devconf cnf;
 struct ipv6_devstat stats;
 struct timer_list rs_timer;
 __u8 rs_probes;
 unsigned long tstamp;
 struct callback_head rcu;
};

struct module_attribute {
 struct attribute attr;
 ssize_t (*show)(struct module_attribute *, struct module_kobject *,
   char *);
 ssize_t (*store)(struct module_attribute *, struct module_kobject *,
    const char *, size_t count);
 void (*setup)(struct module *, const char *);
 int (*test)(struct module *);
 void (*free)(struct module *);
};

struct neigh_table {
 struct neigh_table *next;
 int family;
 int entry_size;
 int key_len;
 __u32 (*hash)(const void *pkey,
     const struct net_device *dev,
     __u32 *hash_rnd);
 int (*constructor)(struct neighbour *);
 int (*pconstructor)(struct pneigh_entry *);
 void (*pdestructor)(struct pneigh_entry *);
 void (*proxy_redo)(struct sk_buff *skb);
 char *id;
 struct neigh_parms parms;
 int gc_interval;
 int gc_thresh1;
 int gc_thresh2;
 int gc_thresh3;
 unsigned long last_flush;
 struct delayed_work gc_work;
 struct timer_list proxy_timer;
 struct sk_buff_head proxy_queue;
 atomic_t entries;
 rwlock_t lock;
 unsigned long last_rand;
 struct neigh_statistics *stats;
 struct neigh_hash_table *nht;
 struct pneigh_entry **phash_buckets;
};

struct pid
{
 atomic_t count;
 unsigned int level;
 struct hlist_head tasks[PIDTYPE_MAX];
 struct callback_head rcu;
 struct upid numbers[1];
};

typedef struct module_attribute module_attribute_no_const;

struct ctl_dir {
 struct ctl_table_header header;
 struct rb_root root;
};

struct fown_struct {
 rwlock_t lock;
 struct pid *pid;
 enum pid_type pid_type;
 kuid_t uid, euid;
 int signum;
};

struct netns_core {
 struct ctl_table_header *sysctl_hdr;
 int sysctl_somaxconn;
 struct prot_inuse *inuse;
};

struct netns_nf {
 struct proc_dir_entry *proc_netfilter;
 const struct nf_logger *nf_loggers[NFPROTO_NUMPROTO];
 struct ctl_table_header *nf_log_dir_header;
};

struct netns_sysctl_ipv6 {
 struct ctl_table_header *hdr;
 struct ctl_table_header *route_hdr;
 struct ctl_table_header *icmp_hdr;
 struct ctl_table_header *frags_hdr;
 struct ctl_table_header *xfrm6_hdr;
 int bindv6only;
 int flush_delay;
 int ip6_rt_max_size;
 int ip6_rt_gc_min_interval;
 int ip6_rt_gc_timeout;
 int ip6_rt_gc_interval;
 int ip6_rt_gc_elasticity;
 int ip6_rt_mtu_expires;
 int ip6_rt_min_advmss;
 int icmpv6_time;
};

struct netns_unix {
 int sysctl_max_dgram_qlen;
 struct ctl_table_header *ctl;
};

struct nf_proto_net {
 struct ctl_table_header *ctl_table_header;
 ctl_table_no_const *ctl_table;
 struct ctl_table_header *ctl_compat_header;
 ctl_table_no_const *ctl_compat_table;
 unsigned int users;
};

struct pid_link
{
 struct hlist_node node;
 struct pid *pid;
};

struct signal_struct {
 atomic_t sigcnt;
 atomic_t live;
 int nr_threads;
 wait_queue_head_t wait_chldexit;
 struct task_struct *curr_target;
 struct sigpending shared_pending;
 int group_exit_code;
 int notify_count;
 struct task_struct *group_exit_task;
 int group_stop_count;
 unsigned int flags;
 unsigned int is_child_subreaper:1;
 unsigned int has_child_subreaper:1;
 int posix_timer_id;
 struct list_head posix_timers;
 struct hrtimer real_timer;
 struct pid *leader_pid;
 ktime_t it_real_incr;
 struct cpu_itimer it[2];
 struct thread_group_cputimer cputimer;
 struct task_cputime cputime_expires;
 struct list_head cpu_timers[3];
 struct pid *tty_old_pgrp;
 int leader;
 struct tty_struct *tty;
 cputime_t utime, stime, cutime, cstime;
 cputime_t gtime;
 cputime_t cgtime;
 struct cputime prev_cputime;
 unsigned long nvcsw, nivcsw, cnvcsw, cnivcsw;
 unsigned long min_flt, maj_flt, cmin_flt, cmaj_flt;
 unsigned long inblock, oublock, cinblock, coublock;
 unsigned long maxrss, cmaxrss;
 struct task_io_accounting ioac;
 unsigned long long sum_sched_runtime;
 struct rlimit rlim[16];
 struct pacct_struct pacct;
 struct taskstats *stats;
 unsigned audit_tty;
 unsigned audit_tty_log_passwd;
 struct tty_audit_buf *tty_audit_buf;
 struct rw_semaphore group_rwsem;
 oom_flags_t oom_flags;
 short oom_score_adj;
 short oom_score_adj_min;
 struct mutex cred_guard_mutex;
};

struct ctl_table_set {
 int (*is_seen)(struct ctl_table_set *);
 struct ctl_dir dir;
};

struct file {
 union {
  struct llist_node fu_llist;
  struct callback_head fu_rcuhead;
 } f_u;
 struct path f_path;
 struct inode *f_inode;
 const struct file_operations *f_op;
 spinlock_t f_lock;
 atomic_long_t f_count;
 unsigned int f_flags;
 fmode_t f_mode;
 loff_t f_pos;
 struct fown_struct f_owner;
 const struct cred *f_cred;
 struct file_ra_state f_ra;
 u64 f_version;
 void *f_security;
 void *private_data;
 struct list_head f_ep_links;
 struct list_head f_tfile_llink;
 struct address_space *f_mapping;
};

struct netns_nf_frag {
 struct netns_sysctl_ipv6 sysctl;
 struct netns_frags frags;
};

struct nf_generic_net {
 struct nf_proto_net pn;
 unsigned int timeout;
};

struct nf_icmp_net {
 struct nf_proto_net pn;
 unsigned int timeout;
};

struct nf_tcp_net {
 struct nf_proto_net pn;
 unsigned int timeouts[TCP_CONNTRACK_TIMEOUT_MAX];
 unsigned int tcp_loose;
 unsigned int tcp_be_liberal;
 unsigned int tcp_max_retrans;
};

struct nf_udp_net {
 struct nf_proto_net pn;
 unsigned int timeouts[UDP_CT_MAX];
};

typedef void (*poll_queue_proc)(struct file *, wait_queue_head_t *, struct poll_table_struct *);

struct coredump_params {
 const siginfo_t *siginfo;
 struct pt_regs *regs;
 struct file *file;
 unsigned long limit;
 unsigned long mm_flags;
 loff_t written;
};

struct ctl_table_root {
 struct ctl_table_set default_set;
 struct ctl_table_set *(*lookup)(struct ctl_table_root *root,
        struct nsproxy *namespaces);
 int (*permissions)(struct ctl_table_header *head, struct ctl_table *table);
};

struct fasync_struct {
 spinlock_t fa_lock;
 int magic;
 int fa_fd;
 struct fasync_struct *fa_next;
 struct file *fa_file;
 struct callback_head fa_rcu;
};

struct iattr {
 unsigned int ia_valid;
 umode_t ia_mode;
 kuid_t ia_uid;
 kgid_t ia_gid;
 loff_t ia_size;
 struct timespec ia_atime;
 struct timespec ia_mtime;
 struct timespec ia_ctime;
 struct file *ia_file;
};

struct kiocb {
 struct file *ki_filp;
 struct kioctx *ki_ctx;
 kiocb_cancel_fn *ki_cancel;
 void *private;
 union {
  void *user;
  struct task_struct *tsk;
 } ki_obj;
 __u64 ki_user_data;
 loff_t ki_pos;
 size_t ki_nbytes;
 struct list_head ki_list;
 struct eventfd_ctx *ki_eventfd;
};

struct nf_ip_net {
 struct nf_generic_net generic;
 struct nf_tcp_net tcp;
 struct nf_udp_net udp;
 struct nf_icmp_net icmp;
 struct nf_icmp_net icmpv6;
 struct ctl_table_header *ctl_table_header;
 ctl_table_no_const *ctl_table;
};

struct vm_area_struct {
 unsigned long vm_start;
 unsigned long vm_end;
 struct vm_area_struct *vm_next, *vm_prev;
 struct rb_node vm_rb;
 unsigned long rb_subtree_gap;
 struct mm_struct *vm_mm;
 pgprot_t vm_page_prot;
 unsigned long vm_flags;
 union {
  struct {
   struct rb_node rb;
   unsigned long rb_subtree_last;
  } linear;
  struct list_head nonlinear;
 } shared;
 struct list_head anon_vma_chain;
 struct anon_vma *anon_vma;
 const struct vm_operations_struct *vm_ops;
 unsigned long vm_pgoff;
 struct file * vm_file;
 struct file *vm_prfile;
 void * vm_private_data;
 struct mempolicy *vm_policy;
 struct vm_area_struct *vm_mirror;
};

typedef struct poll_table_struct {
 poll_queue_proc _qproc;
 unsigned long _key;
} poll_table;

struct address_space_operations {
 int (*writepage)(struct page *page, struct writeback_control *wbc);
 int (*readpage)(struct file *, struct page *);
 int (*writepages)(struct address_space *, struct writeback_control *);
 int (*set_page_dirty)(struct page *page);
 int (*readpages)(struct file *filp, struct address_space *mapping,
   struct list_head *pages, unsigned nr_pages);
 int (*write_begin)(struct file *, struct address_space *mapping,
    loff_t pos, unsigned len, unsigned flags,
    struct page **pagep, void **fsdata);
 int (*write_end)(struct file *, struct address_space *mapping,
    loff_t pos, unsigned len, unsigned copied,
    struct page *page, void *fsdata);
 sector_t (*bmap)(struct address_space *, sector_t);
 void (*invalidatepage) (struct page *, unsigned int, unsigned int);
 int (*releasepage) (struct page *, gfp_t);
 void (*freepage)(struct page *);
 ssize_t (*direct_IO)(int, struct kiocb *, const struct iovec *iov,
   loff_t offset, unsigned long nr_segs);
 int (*get_xip_mem)(struct address_space *, unsigned long, int,
      void **, unsigned long *);
 int (*migratepage) (struct address_space *,
   struct page *, struct page *, enum migrate_mode);
 int (*launder_page) (struct page *);
 int (*is_partially_uptodate) (struct page *, read_descriptor_t *,
     unsigned long);
 void (*is_dirty_writeback) (struct page *, bool *, bool *);
 int (*error_remove_page)(struct address_space *, struct page *);
 int (*swap_activate)(struct swap_info_struct *sis, struct file *file,
    sector_t *span);
 void (*swap_deactivate)(struct file *file);
};

struct bin_attribute {
 struct attribute attr;
 size_t size;
 void *private;
 ssize_t (*read)(struct file *, struct kobject *, struct bin_attribute *,
   char *, loff_t, size_t);
 ssize_t (*write)(struct file *, struct kobject *, struct bin_attribute *,
    char *, loff_t, size_t);
 int (*mmap)(struct file *, struct kobject *, struct bin_attribute *attr,
      struct vm_area_struct *vma);
};

struct dma_map_ops {
 void* (*alloc)(struct device *dev, size_t size,
    dma_addr_t *dma_handle, gfp_t gfp,
    struct dma_attrs *attrs);
 void (*free)(struct device *dev, size_t size,
         void *vaddr, dma_addr_t dma_handle,
         struct dma_attrs *attrs);
 int (*mmap)(struct device *, struct vm_area_struct *,
     void *, dma_addr_t, size_t, struct dma_attrs *attrs);
 int (*get_sgtable)(struct device *dev, struct sg_table *sgt, void *,
      dma_addr_t, size_t, struct dma_attrs *attrs);
 dma_addr_t (*map_page)(struct device *dev, struct page *page,
          unsigned long offset, size_t size,
          enum dma_data_direction dir,
          struct dma_attrs *attrs);
 void (*unmap_page)(struct device *dev, dma_addr_t dma_handle,
      size_t size, enum dma_data_direction dir,
      struct dma_attrs *attrs);
 int (*map_sg)(struct device *dev, struct scatterlist *sg,
        int nents, enum dma_data_direction dir,
        struct dma_attrs *attrs);
 void (*unmap_sg)(struct device *dev,
    struct scatterlist *sg, int nents,
    enum dma_data_direction dir,
    struct dma_attrs *attrs);
 void (*sync_single_for_cpu)(struct device *dev,
        dma_addr_t dma_handle, size_t size,
        enum dma_data_direction dir);
 void (*sync_single_for_device)(struct device *dev,
           dma_addr_t dma_handle, size_t size,
           enum dma_data_direction dir);
 void (*sync_sg_for_cpu)(struct device *dev,
    struct scatterlist *sg, int nents,
    enum dma_data_direction dir);
 void (*sync_sg_for_device)(struct device *dev,
       struct scatterlist *sg, int nents,
       enum dma_data_direction dir);
 int (*mapping_error)(struct device *dev, dma_addr_t dma_addr);
 int (*dma_supported)(struct device *dev, u64 mask);
 int (*set_dma_mask)(struct device *dev, u64 mask);
 int is_phys;
};

struct file_lock {
 struct file_lock *fl_next;
 struct hlist_node fl_link;
 struct list_head fl_block;
 fl_owner_t fl_owner;
 unsigned int fl_flags;
 unsigned char fl_type;
 unsigned int fl_pid;
 int fl_link_cpu;
 struct pid *fl_nspid;
 wait_queue_head_t fl_wait;
 struct file *fl_file;
 loff_t fl_start;
 loff_t fl_end;
 struct fasync_struct * fl_fasync;
 unsigned long fl_break_time;
 unsigned long fl_downgrade_time;
 const struct file_lock_operations *fl_ops;
 const struct lock_manager_operations *fl_lmops;
 union {
  struct nfs_lock_info nfs_fl;
  struct nfs4_lock_info nfs4_fl;
  struct {
   struct list_head link;
   int state;
  } afs;
 } fl_u;
};

struct linux_binprm {
 char buf[128];
 struct vm_area_struct *vma;
 unsigned long vma_pages;
 struct mm_struct *mm;
 unsigned long p;
 unsigned int
  cred_prepared:1,
  cap_effective:1;
 unsigned int recursion_depth;
 struct file * file;
 struct cred *cred;
 int unsafe;
 unsigned int per_clear;
 int argc, envc;
 const char * filename;
 const char * interp;
 unsigned interp_flags;
 unsigned interp_data;
 unsigned long loader, exec;
 char tcomm[16];
};

struct netns_ct {
 atomic_t count;
 unsigned int expect_count;
 unsigned int htable_size;
 struct kmem_cache *nf_conntrack_cachep;
 struct hlist_nulls_head *hash;
 struct hlist_head *expect_hash;
 struct hlist_nulls_head unconfirmed;
 struct hlist_nulls_head dying;
 struct hlist_nulls_head tmpl;
 struct ip_conntrack_stat *stat;
 struct nf_ct_event_notifier *nf_conntrack_event_cb;
 struct nf_exp_event_notifier *nf_expect_event_cb;
 int sysctl_events;
 unsigned int sysctl_events_retry_timeout;
 int sysctl_acct;
 int sysctl_tstamp;
 int sysctl_checksum;
 unsigned int sysctl_log_invalid;
 int sysctl_auto_assign_helper;
 bool auto_assign_helper_warned;
 struct nf_ip_net nf_ct_proto;
 struct hlist_head *nat_bysource;
 unsigned int nat_htable_size;
 struct ctl_table_header *sysctl_header;
 struct ctl_table_header *acct_sysctl_header;
 struct ctl_table_header *tstamp_sysctl_header;
 struct ctl_table_header *event_sysctl_header;
 struct ctl_table_header *helper_sysctl_header;
 char *slabname;
};

struct pipe_inode_info {
 struct mutex mutex;
 wait_queue_head_t wait;
 unsigned int nrbufs, curbuf, buffers;
 atomic_t readers;
 atomic_t writers;
 atomic_t files;
 atomic_t waiting_writers;
 unsigned int r_counter;
 unsigned int w_counter;
 struct page *tmp_page;
 struct fasync_struct *fasync_readers;
 struct fasync_struct *fasync_writers;
 struct pipe_buffer *bufs;
};

struct socket_wq {
 wait_queue_head_t wait;
 struct fasync_struct *fasync_list;
 struct callback_head rcu;
};

struct address_space {
 struct inode *host;
 struct radix_tree_root page_tree;
 spinlock_t tree_lock;
 unsigned int i_mmap_writable;
 struct rb_root i_mmap;
 struct list_head i_mmap_nonlinear;
 struct mutex i_mmap_mutex;
 unsigned long nrpages;
 unsigned long writeback_index;
 const struct address_space_operations *a_ops;
 unsigned long flags;
 struct backing_dev_info *backing_dev_info;
 spinlock_t private_lock;
 struct list_head private_list;
 void *private_data;
};

struct attribute_group {
 const char *name;
 umode_t (*is_visible)(struct kobject *,
           struct attribute *, int);
 struct attribute **attrs;
 struct bin_attribute **bin_attrs;
};

struct dev_archdata {
 struct dma_map_ops *dma_ops;
 void *iommu;
};

struct pipe_buf_operations {
 int can_merge;
 void * (*map)(struct pipe_inode_info *, struct pipe_buffer *, int);
 void (*unmap)(struct pipe_inode_info *, struct pipe_buffer *, void *);
 int (*confirm)(struct pipe_inode_info *, struct pipe_buffer *);
 void (*release)(struct pipe_inode_info *, struct pipe_buffer *);
 int (*steal)(struct pipe_inode_info *, struct pipe_buffer *);
 void (*get)(struct pipe_inode_info *, struct pipe_buffer *);
};

struct bus_type {
 const char *name;
 const char *dev_name;
 struct device *dev_root;
 struct device_attribute *dev_attrs;
 const struct attribute_group **bus_groups;
 const struct attribute_group **dev_groups;
 const struct attribute_group **drv_groups;
 int (*match)(struct device *dev, struct device_driver *drv);
 int (*uevent)(struct device *dev, struct kobj_uevent_env *env);
 int (*probe)(struct device *dev);
 int (*remove)(struct device *dev);
 void (*shutdown)(struct device *dev);
 int (*online)(struct device *dev);
 int (*offline)(struct device *dev);
 int (*suspend)(struct device *dev, pm_message_t state);
 int (*resume)(struct device *dev);
 const struct dev_pm_ops *pm;
 struct iommu_ops *iommu_ops;
 struct subsys_private *p;
 struct lock_class_key lock_key;
};

struct device_type {
 const char *name;
 const struct attribute_group **groups;
 int (*uevent)(struct device *dev, struct kobj_uevent_env *env);
 char *(*devnode)(struct device *dev, umode_t *mode,
    kuid_t *uid, kgid_t *gid);
 void (*release)(struct device *dev);
 const struct dev_pm_ops *pm;
};

struct inode {
 umode_t i_mode;
 unsigned short i_opflags;
 kuid_t i_uid;
 kgid_t i_gid;
 unsigned int i_flags;
 struct posix_acl *i_acl;
 struct posix_acl *i_default_acl;
 const struct inode_operations *i_op;
 struct super_block *i_sb;
 struct address_space *i_mapping;
 void *i_security;
 unsigned long i_ino;
 union {
  const unsigned int i_nlink;
  unsigned int __i_nlink;
 };
 dev_t i_rdev;
 loff_t i_size;
 struct timespec i_atime;
 struct timespec i_mtime;
 struct timespec i_ctime;
 spinlock_t i_lock;
 unsigned short i_bytes;
 unsigned int i_blkbits;
 blkcnt_t i_blocks;
 unsigned long i_state;
 struct mutex i_mutex;
 unsigned long dirtied_when;
 struct hlist_node i_hash;
 struct list_head i_wb_list;
 struct list_head i_lru;
 struct list_head i_sb_list;
 union {
  struct hlist_head i_dentry;
  struct callback_head i_rcu;
 };
 u64 i_version;
 atomic_t i_count;
 atomic_t i_dio_count;
 atomic_t i_writecount;
 const struct file_operations *i_fop;
 struct file_lock *i_flock;
 struct address_space i_data;
 struct dquot *i_dquot[2];
 struct list_head i_devices;
 union {
  struct pipe_inode_info *i_pipe;
  struct block_device *i_bdev;
  struct cdev *i_cdev;
 };
 __u32 i_generation;
 __u32 i_fsnotify_mask;
 struct hlist_head i_fsnotify_marks;
 void *i_private;
};

struct dquot_operations {
 int (*write_dquot) (struct dquot *);
 struct dquot *(*alloc_dquot)(struct super_block *, int);
 void (*destroy_dquot)(struct dquot *);
 int (*acquire_dquot) (struct dquot *);
 int (*release_dquot) (struct dquot *);
 int (*mark_dirty) (struct dquot *);
 int (*write_info) (struct super_block *, int);
 qsize_t *(*get_reserved_space) (struct inode *);
};

struct file_operations {
 struct module *owner;
 loff_t (*llseek) (struct file *, loff_t, int);
 ssize_t (*read) (struct file *, char *, size_t, loff_t *);
 ssize_t (*write) (struct file *, const char *, size_t, loff_t *);
 ssize_t (*aio_read) (struct kiocb *, const struct iovec *, unsigned long, loff_t);
 ssize_t (*aio_write) (struct kiocb *, const struct iovec *, unsigned long, loff_t);
 int (*iterate) (struct file *, struct dir_context *);
 unsigned int (*poll) (struct file *, struct poll_table_struct *);
 long (*unlocked_ioctl) (struct file *, unsigned int, unsigned long);
 long (*compat_ioctl) (struct file *, unsigned int, unsigned long);
 int (*mmap) (struct file *, struct vm_area_struct *);
 int (*open) (struct inode *, struct file *);
 int (*flush) (struct file *, fl_owner_t id);
 int (*release) (struct inode *, struct file *);
 int (*fsync) (struct file *, loff_t, loff_t, int datasync);
 int (*aio_fsync) (struct kiocb *, int datasync);
 int (*fasync) (int, struct file *, int);
 int (*lock) (struct file *, int, struct file_lock *);
 ssize_t (*sendpage) (struct file *, struct page *, int, size_t, loff_t *, int);
 unsigned long (*get_unmapped_area)(struct file *, unsigned long, unsigned long, unsigned long, unsigned long);
 int (*check_flags)(int);
 int (*flock) (struct file *, int, struct file_lock *);
 ssize_t (*splice_write)(struct pipe_inode_info *, struct file *, loff_t *, size_t, unsigned int);
 ssize_t (*splice_read)(struct file *, loff_t *, struct pipe_inode_info *, size_t, unsigned int);
 int (*setlease)(struct file *, long, struct file_lock **);
 long (*fallocate)(struct file *file, int mode, loff_t offset,
     loff_t len);
 int (*show_fdinfo)(struct seq_file *m, struct file *f);
};

struct nameidata {
 struct path path;
 struct qstr last;
 struct path root;
 struct inode *inode;
 unsigned int flags;
 unsigned seq, m_seq;
 int last_type;
 unsigned depth;
 const char *saved_names[MAX_NESTED_LINKS + 1];
};

struct super_operations {
    struct inode *(*alloc_inode)(struct super_block *sb);
 void (*destroy_inode)(struct inode *);
    void (*dirty_inode) (struct inode *, int flags);
 int (*write_inode) (struct inode *, struct writeback_control *wbc);
 int (*drop_inode) (struct inode *);
 void (*evict_inode) (struct inode *);
 void (*put_super) (struct super_block *);
 int (*sync_fs)(struct super_block *sb, int wait);
 int (*freeze_fs) (struct super_block *);
 int (*unfreeze_fs) (struct super_block *);
 int (*statfs) (struct dentry *, struct kstatfs *);
 int (*remount_fs) (struct super_block *, int *, char *);
 void (*umount_begin) (struct super_block *);
 int (*show_options)(struct seq_file *, struct dentry *);
 int (*show_devname)(struct seq_file *, struct dentry *);
 int (*show_path)(struct seq_file *, struct dentry *);
 int (*show_stats)(struct seq_file *, struct dentry *);
 ssize_t (*quota_read)(struct super_block *, int, char *, size_t, loff_t);
 ssize_t (*quota_write)(struct super_block *, int, const char *, size_t, loff_t);
 int (*bdev_try_to_free_page)(struct super_block*, struct page*, gfp_t);
 long (*nr_cached_objects)(struct super_block *, int);
 long (*free_cached_objects)(struct super_block *, long, int);
};

struct inode_operations {
 struct dentry * (*lookup) (struct inode *,struct dentry *, unsigned int);
 void * (*follow_link) (struct dentry *, struct nameidata *);
 int (*permission) (struct inode *, int);
 struct posix_acl * (*get_acl)(struct inode *, int);
 int (*readlink) (struct dentry *, char *,int);
 void (*put_link) (struct dentry *, struct nameidata *, void *);
 int (*create) (struct inode *,struct dentry *, umode_t, bool);
 int (*link) (struct dentry *,struct inode *,struct dentry *);
 int (*unlink) (struct inode *,struct dentry *);
 int (*symlink) (struct inode *,struct dentry *,const char *);
 int (*mkdir) (struct inode *,struct dentry *,umode_t);
 int (*rmdir) (struct inode *,struct dentry *);
 int (*mknod) (struct inode *,struct dentry *,umode_t,dev_t);
 int (*rename) (struct inode *, struct dentry *,
   struct inode *, struct dentry *);
 int (*setattr) (struct dentry *, struct iattr *);
 int (*getattr) (struct vfsmount *mnt, struct dentry *, struct kstat *);
 int (*setxattr) (struct dentry *, const char *,const void *,size_t,int);
 ssize_t (*getxattr) (struct dentry *, const char *, void *, size_t);
 ssize_t (*listxattr) (struct dentry *, char *, size_t);
 int (*removexattr) (struct dentry *, const char *);
 int (*fiemap)(struct inode *, struct fiemap_extent_info *, u64 start,
        u64 len);
 int (*update_time)(struct inode *, struct timespec *, int);
 int (*atomic_open)(struct inode *, struct dentry *,
      struct file *, unsigned open_flag,
      umode_t create_mode, int *opened);
 int (*tmpfile) (struct inode *, struct dentry *, umode_t);
 int (*dentry_open)(struct dentry *, struct file *, const struct cred *);
};

struct module
{
 enum module_state state;
 struct list_head list;
 char name[(64 - sizeof(unsigned long))];
 struct module_kobject mkobj;
 module_attribute_no_const *modinfo_attrs;
 const char *version;
 const char *srcversion;
 struct kobject *holders_dir;
 const struct kernel_symbol *syms;
 const unsigned long *crcs;
 unsigned int num_syms;
 struct kernel_param *kp;
 unsigned int num_kp;
 unsigned int num_gpl_syms;
 const struct kernel_symbol *gpl_syms;
 const unsigned long *gpl_crcs;
 const struct kernel_symbol *gpl_future_syms;
 const unsigned long *gpl_future_crcs;
 unsigned int num_gpl_future_syms;
 unsigned int num_exentries;
 struct exception_table_entry *extable;
 int (*init)(void);
 void *module_init_rx, *module_init_rw;
 void *module_core_rx, *module_core_rw;
 unsigned int init_size_rw, core_size_rw;
 unsigned int init_size_rx, core_size_rx;
 struct mod_arch_specific arch;
 unsigned int taints;
 unsigned num_bugs;
 struct list_head bug_list;
 struct bug_entry *bug_table;
 Elf64_Sym *symtab, *core_symtab;
 unsigned int num_symtab, core_num_syms;
 char *strtab, *core_strtab;
 struct module_sect_attrs *sect_attrs;
 struct module_notes_attrs *notes_attrs;
 char *args;
 void *percpu;
 unsigned int percpu_size;
 unsigned int num_tracepoints;
 struct tracepoint * const *tracepoints_ptrs;
 unsigned int num_trace_bprintk_fmt;
 const char **trace_bprintk_fmt_start;
 struct ftrace_event_call **trace_events;
 unsigned int num_trace_events;
 struct file_operations trace_id;
 struct file_operations trace_enable;
 struct file_operations trace_format;
 struct file_operations trace_filter;
 struct list_head source_list;
 struct list_head target_list;
 void (*exit)(void);
 struct module_ref *refptr;
};

struct class {
 const char *name;
 struct module *owner;
 struct class_attribute *class_attrs;
 const struct attribute_group **dev_groups;
 struct kobject *dev_kobj;
 int (*dev_uevent)(struct device *dev, struct kobj_uevent_env *env);
 char *(*devnode)(struct device *dev, umode_t *mode);
 void (*class_release)(struct class *class);
 void (*dev_release)(struct device *dev);
 int (*suspend)(struct device *dev, pm_message_t state);
 int (*resume)(struct device *dev);
 const struct kobj_ns_type_operations *ns_type;
 const void *(*namespace)(struct device *dev);
 const struct dev_pm_ops *pm;
 struct subsys_private *p;
};

struct device_driver {
 const char *name;
 struct bus_type *bus;
 struct module *owner;
 const char *mod_name;
 bool suppress_bind_attrs;
 const struct of_device_id *of_match_table;
 const struct acpi_device_id *acpi_match_table;
 int (*probe) (struct device *dev);
 int (*remove) (struct device *dev);
 void (*shutdown) (struct device *dev);
 int (*suspend) (struct device *dev, pm_message_t state);
 int (*resume) (struct device *dev);
 const struct attribute_group **groups;
 const struct dev_pm_ops *pm;
 struct driver_private *p;
};

struct exec_domain {
 const char *name;
 handler_t handler;
 unsigned char pers_low;
 unsigned char pers_high;
 unsigned long *signal_map;
 unsigned long *signal_invmap;
 struct map_segment *err_map;
 struct map_segment *socktype_map;
 struct map_segment *sockopt_map;
 struct map_segment *af_map;
 struct module *module;
 struct exec_domain *next;
};

struct file_system_type {
 const char *name;
 int fs_flags;
 struct dentry *(*mount) (struct file_system_type *, int,
         const char *, void *);
 void (*kill_sb) (struct super_block *);
 struct module *owner;
 struct file_system_type * next;
 struct hlist_head fs_supers;
 struct lock_class_key s_lock_key;
 struct lock_class_key s_umount_key;
 struct lock_class_key s_vfs_rename_key;
 struct lock_class_key s_writers_key[(SB_FREEZE_COMPLETE - 1)];
 struct lock_class_key i_lock_key;
 struct lock_class_key i_mutex_key;
 struct lock_class_key i_mutex_dir_key;
};

struct linux_binfmt {
 struct list_head lh;
 struct module *module;
 int (*load_binary)(struct linux_binprm *);
 int (*load_shlib)(struct file *);
 int (*core_dump)(struct coredump_params *cprm);
 void (*handle_mprotect)(struct vm_area_struct *vma, unsigned long newflags);
 unsigned long min_coredump;
};

struct netlink_callback {
 struct sk_buff *skb;
 const struct nlmsghdr *nlh;
 int (*dump)(struct sk_buff * skb,
     struct netlink_callback *cb);
 int (*done)(struct netlink_callback *cb);
 void *data;
 struct module *module;
 u16 family;
 u16 min_dump_alloc;
 unsigned int prev_seq, seq;
 long args[6];
};

struct proto {
 void (*close)(struct sock *sk,
     long timeout);
 int (*connect)(struct sock *sk,
     struct sockaddr *uaddr,
     int addr_len);
 int (*disconnect)(struct sock *sk, int flags);
 struct sock * (*accept)(struct sock *sk, int flags, int *err);
 int (*ioctl)(struct sock *sk, int cmd,
      unsigned long arg);
 int (*init)(struct sock *sk);
 void (*destroy)(struct sock *sk);
 void (*shutdown)(struct sock *sk, int how);
 int (*setsockopt)(struct sock *sk, int level,
     int optname, char *optval,
     unsigned int optlen);
 int (*getsockopt)(struct sock *sk, int level,
     int optname, char *optval,
     int *option);
 int (*compat_setsockopt)(struct sock *sk,
     int level,
     int optname, char *optval,
     unsigned int optlen);
 int (*compat_getsockopt)(struct sock *sk,
     int level,
     int optname, char *optval,
     int *option);
 int (*compat_ioctl)(struct sock *sk,
     unsigned int cmd, unsigned long arg);
 int (*sendmsg)(struct kiocb *iocb, struct sock *sk,
        struct msghdr *msg, size_t len);
 int (*recvmsg)(struct kiocb *iocb, struct sock *sk,
        struct msghdr *msg,
        size_t len, int noblock, int flags,
        int *addr_len);
 int (*sendpage)(struct sock *sk, struct page *page,
     int offset, size_t size, int flags);
 int (*bind)(struct sock *sk,
     struct sockaddr *uaddr, int addr_len);
 int (*backlog_rcv) (struct sock *sk,
      struct sk_buff *skb);
 void (*release_cb)(struct sock *sk);
 void (*mtu_reduced)(struct sock *sk);
 void (*hash)(struct sock *sk);
 void (*unhash)(struct sock *sk);
 void (*rehash)(struct sock *sk);
 int (*get_port)(struct sock *sk, unsigned short snum);
 void (*clear_sk)(struct sock *sk, int size);
 unsigned int inuse_idx;
 bool (*stream_memory_free)(const struct sock *sk);
 void (*enter_memory_pressure)(struct sock *sk);
 atomic_long_t *memory_allocated;
 struct percpu_counter *sockets_allocated;
 int *memory_pressure;
 long *sysctl_mem;
 int *sysctl_wmem;
 int *sysctl_rmem;
 int max_header;
 bool no_autobind;
 struct kmem_cache *slab;
 unsigned int obj_size;
 int slab_flags;
 struct percpu_counter *orphan_count;
 struct request_sock_ops *rsk_prot;
 struct timewait_sock_ops *twsk_prot;
 union {
  struct inet_hashinfo *hashinfo;
  struct udp_table *udp_table;
  struct raw_hashinfo *raw_hash;
 } h;
 struct module *owner;
 char name[32];
 struct list_head node;
};

struct proto_ops {
 int family;
 struct module *owner;
 int (*release) (struct socket *sock);
 int (*bind) (struct socket *sock,
          struct sockaddr *myaddr,
          int sockaddr_len);
 int (*connect) (struct socket *sock,
          struct sockaddr *vaddr,
          int sockaddr_len, int flags);
 int (*socketpair)(struct socket *sock1,
          struct socket *sock2);
 int (*accept) (struct socket *sock,
          struct socket *newsock, int flags);
 int (*getname) (struct socket *sock,
          struct sockaddr *addr,
          int *sockaddr_len, int peer);
 unsigned int (*poll) (struct file *file, struct socket *sock,
          struct poll_table_struct *wait);
 int (*ioctl) (struct socket *sock, unsigned int cmd,
          unsigned long arg);
 int (*compat_ioctl) (struct socket *sock, unsigned int cmd,
          unsigned long arg);
 int (*listen) (struct socket *sock, int len);
 int (*shutdown) (struct socket *sock, int flags);
 int (*setsockopt)(struct socket *sock, int level,
          int optname, char *optval, unsigned int optlen);
 int (*getsockopt)(struct socket *sock, int level,
          int optname, char *optval, int *optlen);
 int (*compat_setsockopt)(struct socket *sock, int level,
          int optname, char *optval, unsigned int optlen);
 int (*compat_getsockopt)(struct socket *sock, int level,
          int optname, char *optval, int *optlen);
 int (*sendmsg) (struct kiocb *iocb, struct socket *sock,
          struct msghdr *m, size_t total_len);
 int (*recvmsg) (struct kiocb *iocb, struct socket *sock,
          struct msghdr *m, size_t total_len,
          int flags);
 int (*mmap) (struct file *file, struct socket *sock,
          struct vm_area_struct * vma);
 ssize_t (*sendpage) (struct socket *sock, struct page *page,
          int offset, size_t size, int flags);
 ssize_t (*splice_read)(struct socket *sock, loff_t *ppos,
           struct pipe_inode_info *pipe, size_t len, unsigned int flags);
 int (*set_peek_off)(struct sock *sk, int val);
};

struct quota_format_type {
 int qf_fmt_id;
 const struct quota_format_ops *qf_ops;
 struct module *qf_owner;
 struct quota_format_type *qf_next;
};

struct device {
 struct device *parent;
 struct device_private *p;
 struct kobject kobj;
 const char *init_name;
 const struct device_type *type;
 struct mutex mutex;
 struct bus_type *bus;
 struct device_driver *driver;
 void *platform_data;
 struct dev_pm_info power;
 struct dev_pm_domain *pm_domain;
 int numa_node;
 u64 *dma_mask;
 u64 coherent_dma_mask;
 struct device_dma_parameters *dma_parms;
 struct list_head dma_pools;
 struct dma_coherent_mem *dma_mem;
 struct dev_archdata archdata;
 struct device_node *of_node;
 struct acpi_dev_node acpi_node;
 dev_t devt;
 u32 id;
 spinlock_t devres_lock;
 struct list_head devres_head;
 struct klist_node knode_class;
 struct class *class;
 const struct attribute_group **groups;
 void (*release)(struct device *dev);
 struct iommu_group *iommu_group;
 bool offline_disabled:1;
 bool offline:1;
};

struct mem_dqinfo {
 struct quota_format_type *dqi_format;
 int dqi_fmt_id;
 struct list_head dqi_dirty_list;
 unsigned long dqi_flags;
 unsigned int dqi_bgrace;
 unsigned int dqi_igrace;
 qsize_t dqi_maxblimit;
 qsize_t dqi_maxilimit;
 void *dqi_priv;
};

struct net_device_ops {
 int (*ndo_init)(struct net_device *dev);
 void (*ndo_uninit)(struct net_device *dev);
 int (*ndo_open)(struct net_device *dev);
 int (*ndo_stop)(struct net_device *dev);
 netdev_tx_t (*ndo_start_xmit) (struct sk_buff *skb,
         struct net_device *dev);
 u16 (*ndo_select_queue)(struct net_device *dev,
          struct sk_buff *skb,
          void *accel_priv);
 void (*ndo_change_rx_flags)(struct net_device *dev,
             int flags);
 void (*ndo_set_rx_mode)(struct net_device *dev);
 int (*ndo_set_mac_address)(struct net_device *dev,
             void *addr);
 int (*ndo_validate_addr)(struct net_device *dev);
 int (*ndo_do_ioctl)(struct net_device *dev,
             struct ifreq *ifr, int cmd);
 int (*ndo_set_config)(struct net_device *dev,
               struct ifmap *map);
 int (*ndo_change_mtu)(struct net_device *dev,
        int new_mtu);
 int (*ndo_neigh_setup)(struct net_device *dev,
         struct neigh_parms *);
 void (*ndo_tx_timeout) (struct net_device *dev);
 struct rtnl_link_stats64* (*ndo_get_stats64)(struct net_device *dev,
           struct rtnl_link_stats64 *storage);
 struct net_device_stats* (*ndo_get_stats)(struct net_device *dev);
 int (*ndo_vlan_rx_add_vid)(struct net_device *dev,
             __be16 proto, u16 vid);
 int (*ndo_vlan_rx_kill_vid)(struct net_device *dev,
              __be16 proto, u16 vid);
 void (*ndo_poll_controller)(struct net_device *dev);
 int (*ndo_netpoll_setup)(struct net_device *dev,
           struct netpoll_info *info,
           gfp_t gfp);
 void (*ndo_netpoll_cleanup)(struct net_device *dev);
 int (*ndo_busy_poll)(struct napi_struct *dev);
 int (*ndo_set_vf_mac)(struct net_device *dev,
        int queue, u8 *mac);
 int (*ndo_set_vf_vlan)(struct net_device *dev,
         int queue, u16 vlan, u8 qos);
 int (*ndo_set_vf_tx_rate)(struct net_device *dev,
            int vf, int rate);
 int (*ndo_set_vf_spoofchk)(struct net_device *dev,
             int vf, bool setting);
 int (*ndo_get_vf_config)(struct net_device *dev,
           int vf,
           struct ifla_vf_info *ivf);
 int (*ndo_set_vf_link_state)(struct net_device *dev,
        int vf, int link_state);
 int (*ndo_set_vf_port)(struct net_device *dev,
         int vf,
         struct nlattr *port[]);
 int (*ndo_get_vf_port)(struct net_device *dev,
         int vf, struct sk_buff *skb);
 int (*ndo_setup_tc)(struct net_device *dev, u8 tc);
 int (*ndo_rx_flow_steer)(struct net_device *dev,
           const struct sk_buff *skb,
           u16 rxq_index,
           u32 flow_id);
 int (*ndo_add_slave)(struct net_device *dev,
       struct net_device *slave_dev);
 int (*ndo_del_slave)(struct net_device *dev,
       struct net_device *slave_dev);
 netdev_features_t (*ndo_fix_features)(struct net_device *dev,
          netdev_features_t features);
 int (*ndo_set_features)(struct net_device *dev,
          netdev_features_t features);
 int (*ndo_neigh_construct)(struct neighbour *n);
 void (*ndo_neigh_destroy)(struct neighbour *n);
 int (*ndo_fdb_add)(struct ndmsg *ndm,
            struct nlattr *tb[],
            struct net_device *dev,
            const unsigned char *addr,
            u16 flags);
 int (*ndo_fdb_del)(struct ndmsg *ndm,
            struct nlattr *tb[],
            struct net_device *dev,
            const unsigned char *addr);
 int (*ndo_fdb_dump)(struct sk_buff *skb,
      struct netlink_callback *cb,
      struct net_device *dev,
      int idx);
 int (*ndo_bridge_setlink)(struct net_device *dev,
            struct nlmsghdr *nlh);
 int (*ndo_bridge_getlink)(struct sk_buff *skb,
            u32 pid, u32 seq,
            struct net_device *dev,
            u32 filter_mask);
 int (*ndo_bridge_dellink)(struct net_device *dev,
            struct nlmsghdr *nlh);
 int (*ndo_change_carrier)(struct net_device *dev,
            bool new_carrier);
 int (*ndo_get_phys_port_id)(struct net_device *dev,
       struct netdev_phys_port_id *ppid);
 void (*ndo_add_vxlan_port)(struct net_device *dev,
            sa_family_t sa_family,
            __be16 port);
 void (*ndo_del_vxlan_port)(struct net_device *dev,
            sa_family_t sa_family,
            __be16 port);
 void* (*ndo_dfwd_add_station)(struct net_device *pdev,
       struct net_device *dev);
 void (*ndo_dfwd_del_station)(struct net_device *pdev,
       void *priv);
 netdev_tx_t (*ndo_dfwd_start_xmit) (struct sk_buff *skb,
       struct net_device *dev,
       void *priv);
};

struct sock_common {
 union {
  __addrpair skc_addrpair;
  struct {
   __be32 skc_daddr;
   __be32 skc_rcv_saddr;
  };
 };
 union {
  unsigned int skc_hash;
  __u16 skc_u16hashes[2];
 };
 union {
  __portpair skc_portpair;
  struct {
   __be16 skc_dport;
   __u16 skc_num;
  };
 };
 unsigned short skc_family;
 volatile unsigned char skc_state;
 unsigned char skc_reuse:4;
 unsigned char skc_reuseport:4;
 int skc_bound_dev_if;
 union {
  struct hlist_node skc_bind_node;
  struct hlist_nulls_node skc_portaddr_node;
 };
 struct proto *skc_prot;
 struct net *skc_net;
 struct in6_addr skc_v6_daddr;
 struct in6_addr skc_v6_rcv_saddr;
 int skc_dontcopy_begin[0];
 union {
  struct hlist_node skc_node;
  struct hlist_nulls_node skc_nulls_node;
 };
 int skc_tx_queue_mapping;
 atomic_t skc_refcnt;
 int skc_dontcopy_end[0];
};

struct socket {
 socket_state state;
 ;
 short type;
 ;
 unsigned long flags;
 struct socket_wq *wq;
 struct file *file;
 struct sock *sk;
 const struct proto_ops *ops;
};

struct thread_info {
 struct exec_domain *exec_domain;
 __u32 flags;
 __u32 status;
 __u32 cpu;
 int saved_preempt_count;
 mm_segment_t addr_limit;
 struct restart_block restart_block;
 void *sysenter_return;
 unsigned long lowest_stack;
 unsigned int sig_on_uaccess_error:1;
 unsigned int uaccess_err:1;
};

struct quota_info {
 unsigned int flags;
 struct mutex dqio_mutex;
 struct mutex dqonoff_mutex;
 struct rw_semaphore dqptr_sem;
 struct inode *files[2];
 struct mem_dqinfo info[2];
 const struct quota_format_ops *ops[2];
};

struct sock {
 struct sock_common __sk_common;
 socket_lock_t sk_lock;
 struct sk_buff_head sk_receive_queue;
 struct {
  atomic_t rmem_alloc;
  int len;
  struct sk_buff *head;
  struct sk_buff *tail;
 } sk_backlog;
 int sk_forward_alloc;
 __u32 sk_rxhash;
 unsigned int sk_napi_id;
 unsigned int sk_ll_usec;
 atomic_unchecked_t sk_drops;
 int sk_rcvbuf;
 struct sk_filter *sk_filter;
 struct socket_wq *sk_wq;
 struct xfrm_policy *sk_policy[2];
 unsigned long sk_flags;
 struct dst_entry *sk_rx_dst;
 struct dst_entry *sk_dst_cache;
 spinlock_t sk_dst_lock;
 atomic_t sk_wmem_alloc;
 atomic_t sk_omem_alloc;
 int sk_sndbuf;
 struct sk_buff_head sk_write_queue;
 ;
 unsigned int sk_shutdown : 2,
    sk_no_check : 2,
    sk_userlocks : 4,
    sk_protocol : 8,
    sk_type : 16;
 ;
 int sk_wmem_queued;
 gfp_t sk_allocation;
 u32 sk_pacing_rate;
 u32 sk_max_pacing_rate;
 netdev_features_t sk_route_caps;
 netdev_features_t sk_route_nocaps;
 int sk_gso_type;
 unsigned int sk_gso_max_size;
 u16 sk_gso_max_segs;
 int sk_rcvlowat;
 unsigned long sk_lingertime;
 struct sk_buff_head sk_error_queue;
 struct proto *sk_prot_creator;
 rwlock_t sk_callback_lock;
 int sk_err,
    sk_err_soft;
 unsigned short sk_ack_backlog;
 unsigned short sk_max_ack_backlog;
 __u32 sk_priority;
 struct pid *sk_peer_pid;
 const struct cred *sk_peer_cred;
 long sk_rcvtimeo;
 long sk_sndtimeo;
 void *sk_protinfo;
 struct timer_list sk_timer;
 ktime_t sk_stamp;
 struct socket *sk_socket;
 void *sk_user_data;
 struct page_frag sk_frag;
 struct sk_buff *sk_send_head;
 __s32 sk_peek_off;
 int sk_write_pending;
 void *sk_security;
 __u32 sk_mark;
 u32 sk_classid;
 struct cg_proto *sk_cgrp;
 void (*sk_state_change)(struct sock *sk);
 void (*sk_data_ready)(struct sock *sk, int bytes);
 void (*sk_write_space)(struct sock *sk);
 void (*sk_error_report)(struct sock *sk);
 int (*sk_backlog_rcv)(struct sock *sk,
        struct sk_buff *skb);
 void (*sk_destruct)(struct sock *sk);
};

struct task_struct {
 volatile long state;
 void *stack;
 atomic_t usage;
 unsigned int flags;
 unsigned int ptrace;
 struct llist_node wake_entry;
 int on_cpu;
 struct task_struct *last_wakee;
 unsigned long wakee_flips;
 unsigned long wakee_flip_decay_ts;
 int wake_cpu;
 int on_rq;
 int prio, static_prio, normal_prio;
 unsigned int rt_priority;
 const struct sched_class *sched_class;
 struct sched_entity se;
 struct sched_rt_entity rt;
 struct task_group *sched_task_group;
 unsigned int btrace_seq;
 unsigned int policy;
 int nr_cpus_allowed;
 cpumask_t cpus_allowed;
 struct sched_info sched_info;
 struct list_head tasks;
 struct plist_node pushable_tasks;
 struct mm_struct *mm, *active_mm;
 struct task_rss_stat rss_stat;
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
 struct task_struct *real_parent;
 struct task_struct *parent;
 struct list_head children;
 struct list_head sibling;
 struct task_struct *group_leader;
 struct list_head ptraced;
 struct list_head ptrace_entry;
 struct pid_link pids[PIDTYPE_MAX];
 struct list_head thread_group;
 struct completion *vfork_done;
 pid_t *set_child_tid;
 pid_t *clear_child_tid;
 cputime_t utime, stime, utimescaled, stimescaled;
 cputime_t gtime;
 struct cputime prev_cputime;
 unsigned long nvcsw, nivcsw;
 struct timespec start_time;
 struct timespec real_start_time;
 unsigned long min_flt, maj_flt;
 struct task_cputime cputime_expires;
 struct list_head cpu_timers[3];
 const struct cred *real_cred;
 const struct cred *cred;
 char comm[16];
 int link_count, total_link_count;
 struct sysv_sem sysvsem;
 struct thread_struct thread;
 struct thread_info tinfo;
 struct fs_struct *fs;
 struct files_struct *files;
 struct nsproxy *nsproxy;
 struct signal_struct *signal;
 struct sighand_struct *sighand;
 sigset_t blocked, real_blocked;
 sigset_t saved_sigmask;
 struct sigpending pending;
 unsigned long sas_ss_sp;
 size_t sas_ss_size;
 int (*notifier)(void *priv);
 void *notifier_data;
 sigset_t *notifier_mask;
 struct callback_head *task_works;
 struct audit_context *audit_context;
 kuid_t loginuid;
 unsigned int sessionid;
 struct seccomp seccomp;
    u32 parent_exec_id;
    u32 self_exec_id;
 spinlock_t alloc_lock;
 raw_spinlock_t pi_lock;
 struct plist_head pi_waiters;
 struct rt_mutex_waiter *pi_blocked_on;
 void *journal_info;
 struct bio_list *bio_list;
 struct blk_plug *plug;
 struct reclaim_state *reclaim_state;
 struct backing_dev_info *backing_dev_info;
 struct io_context *io_context;
 unsigned long ptrace_message;
 siginfo_t *last_siginfo;
 struct task_io_accounting ioac;
 u64 acct_rss_mem1;
 u64 acct_vm_mem1;
 cputime_t acct_timexpd;
 nodemask_t mems_allowed;
 seqcount_t mems_allowed_seq;
 int cpuset_mem_spread_rotor;
 int cpuset_slab_spread_rotor;
 struct css_set *cgroups;
 struct list_head cg_list;
 struct robust_list_head *robust_list;
 struct compat_robust_list_head *compat_robust_list;
 struct list_head pi_state_list;
 struct futex_pi_state *pi_state_cache;
 struct perf_event_context *perf_event_ctxp[perf_nr_task_contexts];
 struct mutex perf_event_mutex;
 struct list_head perf_event_list;
 struct mempolicy *mempolicy;
 short il_next;
 short pref_node_fork;
 struct callback_head rcu;
 struct pipe_inode_info *splice_pipe;
 struct page_frag task_frag;
 struct task_delay_info *delays;
 int nr_dirtied;
 int nr_dirtied_pause;
 unsigned long dirty_paused_when;
 unsigned long timer_slack_ns;
 unsigned long default_timer_slack_ns;
 unsigned long trace;
 unsigned long trace_recursion;
 u32 audit_ctx[2];
};

struct core_thread {
 struct task_struct *task;
 struct core_thread *next;
};

struct dst_ops {
 unsigned short family;
 __be16 protocol;
 unsigned int gc_thresh;
 int (*gc)(struct dst_ops *ops);
 struct dst_entry * (*check)(struct dst_entry *, __u32 cookie);
 unsigned int (*default_advmss)(const struct dst_entry *);
 unsigned int (*mtu)(const struct dst_entry *);
 u32 * (*cow_metrics)(struct dst_entry *, unsigned long);
 void (*destroy)(struct dst_entry *);
 void (*ifdown)(struct dst_entry *,
       struct net_device *dev, int how);
 struct dst_entry * (*negative_advice)(struct dst_entry *);
 void (*link_failure)(struct sk_buff *);
 void (*update_pmtu)(struct dst_entry *dst, struct sock *sk,
            struct sk_buff *skb, u32 mtu);
 void (*redirect)(struct dst_entry *dst, struct sock *sk,
         struct sk_buff *skb);
 int (*local_out)(struct sk_buff *skb);
 struct neighbour * (*neigh_lookup)(const struct dst_entry *dst,
      struct sk_buff *skb,
      const void *daddr);
 struct kmem_cache *kmem_cachep;
 struct percpu_counter pcpuc_entries ;
};

struct netns_ipv4 {
 struct ctl_table_header *forw_hdr;
 struct ctl_table_header *frags_hdr;
 struct ctl_table_header *ipv4_hdr;
 struct ctl_table_header *route_hdr;
 struct ctl_table_header *xfrm4_hdr;
 struct ipv4_devconf *devconf_all;
 struct ipv4_devconf *devconf_dflt;
 struct fib_rules_ops *rules_ops;
 bool fib_has_custom_rules;
 struct fib_table *fib_local;
 struct fib_table *fib_main;
 struct fib_table *fib_default;
 struct hlist_head *fib_table_hash;
 struct sock *fibnl;
 struct sock **icmp_sk;
 struct inet_peer_base *peers;
 struct tcpm_hash_bucket *tcp_metrics_hash;
 unsigned int tcp_metrics_hash_log;
 struct netns_frags frags;
 struct xt_table *iptable_filter;
 struct xt_table *iptable_mangle;
 struct xt_table *iptable_raw;
 struct xt_table *arptable_filter;
 struct xt_table *iptable_security;
 struct xt_table *nat_table;
 int sysctl_icmp_echo_ignore_all;
 int sysctl_icmp_echo_ignore_broadcasts;
 int sysctl_icmp_ignore_bogus_error_responses;
 int sysctl_icmp_ratelimit;
 int sysctl_icmp_ratemask;
 int sysctl_icmp_errors_use_inbound_ifaddr;
 struct local_ports sysctl_local_ports;
 int sysctl_tcp_ecn;
 kgid_t sysctl_ping_group_range[2];
 atomic_unchecked_t dev_addr_genid;
 struct mr_table *mrt;
 atomic_unchecked_t rt_genid;
};

struct request_sock {
 struct sock_common __req_common;
 struct request_sock *dl_next;
 u16 mss;
 u8 num_retrans;
 u8 cookie_ts:1;
 u8 num_timeout:7;
 u32 window_clamp;
 u32 rcv_wnd;
 u32 ts_recent;
 unsigned long expires;
 const struct request_sock_ops *rsk_ops;
 struct sock *sk;
 u32 secid;
 u32 peer_secid;
 unsigned char aux[32];
};

struct super_block {
 struct list_head s_list;
 dev_t s_dev;
 unsigned char s_blocksize_bits;
 unsigned long s_blocksize;
 loff_t s_maxbytes;
 struct file_system_type *s_type;
 const struct super_operations *s_op;
 const struct dquot_operations *dq_op;
 const struct quotactl_ops *s_qcop;
 const struct export_operations *s_export_op;
 unsigned long s_flags;
 unsigned long s_magic;
 struct dentry *s_root;
 struct rw_semaphore s_umount;
 int s_count;
 atomic_t s_active;
 void *s_security;
 const struct xattr_handler **s_xattr;
 struct list_head s_inodes;
 struct hlist_bl_head s_anon;
 struct list_head s_mounts;
 struct block_device *s_bdev;
 struct backing_dev_info *s_bdi;
 struct mtd_info *s_mtd;
 struct hlist_node s_instances;
 struct quota_info s_dquot;
 struct sb_writers s_writers;
 char s_id[32];
 u8 s_uuid[16];
 void *s_fs_info;
 unsigned int s_max_links;
 fmode_t s_mode;
 u32 s_time_gran;
 struct mutex s_vfs_rename_mutex;
 char *s_subtype;
 char *s_options;
 const struct dentry_operations *s_d_op;
 int cleancache_poolid;
 struct shrinker s_shrink;
 atomic_long_t s_remove_count;
 int s_readonly_remount;
 struct workqueue_struct *s_dio_done_wq;
 struct list_lru s_dentry_lru ;
 struct list_lru s_inode_lru ;
 struct callback_head rcu;
 int s_stack_depth;
 int forced_mac_level;
 int forced_mac_category;
 int forced_mac_inited;
        unsigned int s_secdel_rounds;
};

struct cgroupfs_root {
 struct super_block *sb;
 unsigned long subsys_mask;
 int hierarchy_id;
 struct list_head subsys_list;
 struct cgroup top_cgroup;
 int number_of_cgroups;
 struct list_head root_list;
 unsigned long flags;
 struct idr cgroup_idr;
 char release_agent_path[4096];
 char name[64];
};

struct core_state {
 atomic_t nr_threads;
 struct core_thread dumper;
 struct completion startup;
};

struct netns_ipv6 {
 struct netns_sysctl_ipv6 sysctl;
 struct ipv6_devconf *devconf_all;
 struct ipv6_devconf *devconf_dflt;
 struct inet_peer_base *peers;
 struct netns_frags frags;
 struct xt_table *ip6table_filter;
 struct xt_table *ip6table_mangle;
 struct xt_table *ip6table_raw;
 struct xt_table *ip6table_security;
 struct xt_table *ip6table_nat;
 struct rt6_info *ip6_null_entry;
 struct rt6_statistics *rt6_stats;
 struct timer_list ip6_fib_timer;
 struct hlist_head *fib_table_hash;
 struct fib6_table *fib6_main_tbl;
 struct dst_ops ip6_dst_ops;
 unsigned int ip6_rt_gc_expire;
 unsigned long ip6_rt_last_gc;
 struct sock **icmp_sk;
 struct sock *ndisc_sk;
 struct sock *tcp_sk;
 struct sock *igmp_sk;
 atomic_unchecked_t dev_addr_genid;
 atomic_unchecked_t rt_genid;
};

struct netns_xfrm {
 struct list_head state_all;
 struct hlist_head *state_bydst;
 struct hlist_head *state_bysrc;
 struct hlist_head *state_byspi;
 unsigned int state_hmask;
 unsigned int state_num;
 struct work_struct state_hash_work;
 struct hlist_head state_gc_list;
 struct work_struct state_gc_work;
 wait_queue_head_t km_waitq;
 struct list_head policy_all;
 struct hlist_head *policy_byidx;
 unsigned int policy_idx_hmask;
 struct hlist_head policy_inexact[XFRM_POLICY_MAX * 2];
 struct xfrm_policy_hash policy_bydst[XFRM_POLICY_MAX * 2];
 unsigned int policy_count[XFRM_POLICY_MAX * 2];
 struct work_struct policy_hash_work;
 struct sock *nlsk;
 struct sock *nlsk_stash;
 u32 sysctl_aevent_etime;
 u32 sysctl_aevent_rseqth;
 int sysctl_larval_drop;
 u32 sysctl_acq_expires;
 struct ctl_table_header *sysctl_hdr;
 struct dst_ops xfrm4_dst_ops;
 struct dst_ops xfrm6_dst_ops;
};

struct cgroup_subsys {
 struct cgroup_subsys_state *(*css_alloc)(struct cgroup_subsys_state *parent_css);
 int (*css_online)(struct cgroup_subsys_state *css);
 void (*css_offline)(struct cgroup_subsys_state *css);
 void (*css_free)(struct cgroup_subsys_state *css);
 int (*can_attach)(struct cgroup_subsys_state *css,
     struct cgroup_taskset *tset);
 void (*cancel_attach)(struct cgroup_subsys_state *css,
         struct cgroup_taskset *tset);
 void (*attach)(struct cgroup_subsys_state *css,
         struct cgroup_taskset *tset);
 void (*fork)(struct task_struct *task);
 void (*exit)(struct cgroup_subsys_state *css,
       struct cgroup_subsys_state *old_css,
       struct task_struct *task);
 void (*bind)(struct cgroup_subsys_state *root_css);
 int subsys_id;
 int disabled;
 int early_init;
 bool broken_hierarchy;
 bool warned_broken_hierarchy;
 const char *name;
 struct cgroupfs_root *root;
 struct list_head sibling;
 struct list_head cftsets;
 struct cftype *base_cftypes;
 struct cftype_set base_cftset;
 struct module *module;
};

struct mm_struct {
 struct vm_area_struct * mmap;
 struct rb_root mm_rb;
 struct vm_area_struct * mmap_cache;
 unsigned long (*get_unmapped_area) (struct file *filp,
    unsigned long addr, unsigned long len,
    unsigned long pgoff, unsigned long flags);
 unsigned long mmap_base;
 unsigned long mmap_legacy_base;
 unsigned long task_size;
 unsigned long highest_vm_end;
 pgd_t * pgd;
 atomic_t mm_users;
 atomic_t mm_count;
 atomic_long_t nr_ptes;
 int map_count;
 spinlock_t page_table_lock;
 struct rw_semaphore mmap_sem;
 struct list_head mmlist;
 unsigned long hiwater_rss;
 unsigned long hiwater_vm;
 unsigned long total_vm;
 unsigned long locked_vm;
 unsigned long pinned_vm;
 unsigned long shared_vm;
 unsigned long exec_vm;
 unsigned long stack_vm;
 unsigned long def_flags;
 unsigned long start_code, end_code, start_data, end_data;
 unsigned long start_brk, brk, start_stack;
 unsigned long arg_start, arg_end, env_start, env_end;
 unsigned long saved_auxv[(2*(2 + 20 + 1))];
 struct mm_rss_stat rss_stat;
 struct linux_binfmt *binfmt;
 cpumask_var_t cpu_vm_mask_var;
 mm_context_t context;
 unsigned long flags;
 struct core_state *core_state;
 spinlock_t ioctx_lock;
 struct kioctx_table *ioctx_table;
 struct file *exe_file;
 bool tlb_flush_pending;
 struct uprobes_state uprobes_state;
};

struct net {
 atomic_t passive;
 atomic_t count;
 spinlock_t rules_mod_lock;
 struct list_head list;
 struct list_head cleanup_list;
 struct list_head exit_list;
 struct user_namespace *user_ns;
 unsigned int proc_inum;
 struct proc_dir_entry *proc_net;
 struct proc_dir_entry *proc_net_stat;
 struct ctl_table_set sysctls;
 struct sock *rtnl;
 struct sock *genl_sock;
 struct list_head dev_base_head;
 struct hlist_head *dev_name_head;
 struct hlist_head *dev_index_head;
 unsigned int dev_base_seq;
 int ifindex;
 unsigned int dev_unreg_count;
 struct list_head rules_ops;
 struct net_device *loopback_dev;
 struct netns_core core;
 struct netns_mib mib;
 struct netns_packet packet;
 struct netns_unix unx;
 struct netns_ipv4 ipv4;
 struct netns_ipv6 ipv6;
 struct netns_nf nf;
 struct netns_xt xt;
 struct netns_ct ct;
 struct netns_nf_frag nf_frag;
 struct sock *nfnl;
 struct sock *nfnl_stash;
 struct net_generic *gen;
 struct netns_xfrm xfrm;
 struct sock *diag_nlsk;
 atomic_unchecked_t fnhe_genid;
};

struct cftype {
 char name[64];
 int private;
 umode_t mode;
 size_t max_write_len;
 unsigned int flags;
 struct cgroup_subsys *ss;
 int (*open)(struct inode *inode, struct file *file);
 ssize_t (*read)(struct cgroup_subsys_state *css, struct cftype *cft,
   struct file *file,
   char *buf, size_t nbytes, loff_t *ppos);
 u64 (*read_u64)(struct cgroup_subsys_state *css, struct cftype *cft);
 s64 (*read_s64)(struct cgroup_subsys_state *css, struct cftype *cft);
 int (*read_map)(struct cgroup_subsys_state *css, struct cftype *cft,
   struct cgroup_map_cb *cb);
 int (*read_seq_string)(struct cgroup_subsys_state *css,
          struct cftype *cft, struct seq_file *m);
 ssize_t (*write)(struct cgroup_subsys_state *css, struct cftype *cft,
    struct file *file,
    const char *buf, size_t nbytes, loff_t *ppos);
 int (*write_u64)(struct cgroup_subsys_state *css, struct cftype *cft,
    u64 val);
 int (*write_s64)(struct cgroup_subsys_state *css, struct cftype *cft,
    s64 val);
 int (*write_string)(struct cgroup_subsys_state *css, struct cftype *cft,
       const char *buffer);
 int (*trigger)(struct cgroup_subsys_state *css, unsigned int event);
 int (*release)(struct inode *inode, struct file *file);
 int (*register_event)(struct cgroup_subsys_state *css,
         struct cftype *cft, struct eventfd_ctx *eventfd,
         const char *args);
 void (*unregister_event)(struct cgroup_subsys_state *css,
     struct cftype *cft,
     struct eventfd_ctx *eventfd);
};

struct rtnl_link_ops {
 struct list_head list;
 const char *kind;
 size_t priv_size;
 void (*setup)(struct net_device *dev);
 int maxtype;
 const struct nla_policy *policy;
 int (*validate)(struct nlattr *tb[],
         struct nlattr *data[]);
 int (*newlink)(struct net *src_net,
        struct net_device *dev,
        struct nlattr *tb[],
        struct nlattr *data[]);
 int (*changelink)(struct net_device *dev,
           struct nlattr *tb[],
           struct nlattr *data[]);
 void (*dellink)(struct net_device *dev,
        struct list_head *head);
 size_t (*get_size)(const struct net_device *dev);
 int (*fill_info)(struct sk_buff *skb,
          const struct net_device *dev);
 size_t (*get_xstats_size)(const struct net_device *dev);
 int (*fill_xstats)(struct sk_buff *skb,
            const struct net_device *dev);
 unsigned int (*get_num_tx_queues)(void);
 unsigned int (*get_num_rx_queues)(void);
};

struct net_device {
 char name[16];
 struct hlist_node name_hlist;
 char *ifalias;
 unsigned long mem_end;
 unsigned long mem_start;
 unsigned long base_addr;
 int irq;
 unsigned long state;
 struct list_head dev_list;
 struct list_head napi_list;
 struct list_head unreg_list;
 struct list_head close_list;
 struct {
  struct list_head upper;
  struct list_head lower;
 } adj_list;
 struct {
  struct list_head upper;
  struct list_head lower;
 } all_adj_list;
 netdev_features_t features;
 netdev_features_t hw_features;
 netdev_features_t wanted_features;
 netdev_features_t vlan_features;
 netdev_features_t hw_enc_features;
 netdev_features_t mpls_features;
 int ifindex;
 int iflink;
 struct net_device_stats stats;
 atomic_long_unchecked_t rx_dropped;
 const struct net_device_ops *netdev_ops;
 const struct ethtool_ops *ethtool_ops;
 const struct forwarding_accel_ops *fwd_ops;
 const struct header_ops *header_ops;
 unsigned int flags;
 unsigned int priv_flags;
 unsigned short gflags;
 unsigned short padded;
 unsigned char operstate;
 unsigned char link_mode;
 unsigned char if_port;
 unsigned char dma;
 unsigned int mtu;
 unsigned short type;
 unsigned short hard_header_len;
 unsigned short needed_headroom;
 unsigned short needed_tailroom;
 unsigned char perm_addr[32];
 unsigned char addr_assign_type;
 unsigned char addr_len;
 unsigned short neigh_priv_len;
 unsigned short dev_id;
 spinlock_t addr_list_lock;
 struct netdev_hw_addr_list uc;
 struct netdev_hw_addr_list mc;
 struct netdev_hw_addr_list dev_addrs;
 struct kset *queues_kset;
 bool uc_promisc;
 unsigned int promiscuity;
 unsigned int allmulti;
 void *atalk_ptr;
 struct in_device *ip_ptr;
 struct dn_dev *dn_ptr;
 struct inet6_dev *ip6_ptr;
 void *ax25_ptr;
 struct wireless_dev *ieee80211_ptr;
 unsigned long last_rx;
 unsigned char *dev_addr;
 struct netdev_rx_queue *_rx;
 unsigned int num_rx_queues;
 unsigned int real_num_rx_queues;
 rx_handler_func_t *rx_handler;
 void *rx_handler_data;
 struct netdev_queue *ingress_queue;
 unsigned char broadcast[32];
 struct netdev_queue *_tx ;
 unsigned int num_tx_queues;
 unsigned int real_num_tx_queues;
 struct Qdisc *qdisc;
 unsigned long tx_queue_len;
 spinlock_t tx_global_lock;
 struct xps_dev_maps *xps_maps;
 struct cpu_rmap *rx_cpu_rmap;
 unsigned long trans_start;
 int watchdog_timeo;
 struct timer_list watchdog_timer;
 int *pcpu_refcnt;
 struct list_head todo_list;
 struct hlist_node index_hlist;
 struct list_head link_watch_list;
 enum { NETREG_UNINITIALIZED=0,
        NETREG_REGISTERED,
        NETREG_UNREGISTERING,
        NETREG_UNREGISTERED,
        NETREG_RELEASED,
        NETREG_DUMMY,
 } reg_state:8;
 bool dismantle;
 enum {
  RTNL_LINK_INITIALIZED,
  RTNL_LINK_INITIALIZING,
 } rtnl_link_state:16;
 void (*destructor)(struct net_device *dev);
 struct netpoll_info *npinfo;
 struct net *nd_net;
 union {
  void *ml_priv;
  struct pcpu_lstats *lstats;
  struct pcpu_tstats *tstats;
  struct pcpu_dstats *dstats;
  struct pcpu_vstats *vstats;
 };
 struct garp_port *garp_port;
 struct mrp_port *mrp_port;
 struct device dev;
 const struct attribute_group *sysfs_groups[4];
 const struct rtnl_link_ops *rtnl_link_ops;
 unsigned int gso_max_size;
 u16 gso_max_segs;
 u8 num_tc;
 struct netdev_tc_txq tc_to_txq[16];
 u8 prio_tc_map[15 + 1];
 struct phy_device *phydev;
 struct lock_class_key *qdisc_tx_busylock;
 int group;
 struct pm_qos_request pm_qos_req;
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

typedef struct PDP_ROLES_T /*  role label for subjects and objects*/
{
    PDP_ROLE_T*     roles;
    uint32_t        roles_cnt;

    PDP_ROLE_T*     aroles;
    uint32_t        aroles_cnt;

    atomic_t        ucnt;
    struct rcu_head rcu;


} PDP_LROLES_T;

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

typedef struct
{

	const PDPL_T *l;





} parsec_sb_security_t;
//------------------------------------------------------------------------------

/*@ logic parsec_sb_security_t *CONST_SB_SEC{L}(struct super_block* sb) = (parsec_sb_security_t*)(sb->s_security); */
/*@ requires \valid(sb);
    requires \typeof(sb->s_security) <: \type(parsec_sb_security_t*);
    ensures \result == CONST_SB_SEC(sb);
*/
static inline const parsec_sb_security_t* CONST_SB_SEC(const struct super_block* sb) { return (const parsec_sb_security_t*)(sb->s_security); }