#define CONFIG_HZ 1000

#define DEFAULT_RATELIMIT_BURST 10

#define KERN_SOH "\001"

#define SPIN_DEBUG_INIT(lockname) 

#define SPIN_DEP_MAP_INIT(lockname) 

#define __ARCH_SPIN_LOCK_UNLOCKED { { 0 } }

#define HZ CONFIG_HZ

#define KERN_ERR KERN_SOH "3"

#define __RAW_SPIN_LOCK_INITIALIZER(lockname) { .raw_lock = __ARCH_SPIN_LOCK_UNLOCKED, SPIN_DEBUG_INIT(lockname) SPIN_DEP_MAP_INIT(lockname) }

#define DEFAULT_RATELIMIT_INTERVAL (5 * HZ)

#define __RAW_SPIN_LOCK_UNLOCKED(lockname) (raw_spinlock_t) __RAW_SPIN_LOCK_INITIALIZER(lockname)

#define DEFINE_RATELIMIT_STATE(name,interval_init,burst_init) struct ratelimit_state name = { .lock = __RAW_SPIN_LOCK_UNLOCKED(name.lock), .interval = interval_init, .burst = burst_init, }

#define __ratelimit(state) ___ratelimit(state, __func__)

#define printk_ratelimited(fmt,...) ({ static DEFINE_RATELIMIT_STATE(_rs, DEFAULT_RATELIMIT_INTERVAL, DEFAULT_RATELIMIT_BURST); if (__ratelimit(&_rs)) printk(fmt, ##__VA_ARGS__); })

typedef unsigned int __u32;

typedef unsigned short u16;

typedef unsigned char u8;

typedef u8 __ticket_t;

typedef u16 __ticketpair_t;

typedef __u32 uint32_t;

typedef struct arch_spinlock {
 union {
  __ticketpair_t head_tail;
  struct __raw_tickets {
   __ticket_t head, tail;
  } tickets;
 };
} arch_spinlock_t;

typedef struct raw_spinlock {
 arch_spinlock_t raw_lock;
} raw_spinlock_t;

struct ratelimit_state {
 raw_spinlock_t lock;
 int interval;
 int burst;
 int printed;
 int missed;
 unsigned long begin;
};
//------------------------------------------------------------------------------

extern void dump_stack(void);

int printk(const char *fmt, ...);

extern int ___ratelimit(struct ratelimit_state *rs, const char *func);
//------------------------------------------------------------------------------

	#define ASSERT(c) { if(!(c)) { static DEFINE_RATELIMIT_STATE(_rs,DEFAULT_RATELIMIT_INTERVAL,DEFAULT_RATELIMIT_BURST); printk_ratelimited(KERN_ERR "ASSERTION(%s) failed in %s() file: %s, line: %d\n",#c,__func__,__FILE__,__LINE__); if (__ratelimit(&_rs)) dump_stack(); } }

typedef uint32_t	parsec_cap_t;

typedef struct {
	parsec_cap_t	cap_effective;
	parsec_cap_t	cap_permitted;
	parsec_cap_t	cap_inheritable;
} parsec_caps_t;
//------------------------------------------------------------------------------

/*@ requires \valid(tcaps);
	requires \valid(fcaps);
	ensures *tcaps == *fcaps;
	ensures tcaps->cap_effective == fcaps->cap_effective;
	ensures tcaps->cap_permitted == fcaps->cap_permitted;
	ensures tcaps->cap_inheritable == fcaps->cap_inheritable;
*/
void caps_cpy(parsec_caps_t *tcaps, const parsec_caps_t *fcaps)
{
	ASSERT(tcaps);
	ASSERT(fcaps);
	*tcaps = *fcaps;
/*	caps->cap_inheritable = TASK_CAP_INH(tsk);
	caps->cap_permitted = TASK_CAP_PRM(tsk);
	caps->cap_effective = TASK_CAP_EFF(tsk);*/
}