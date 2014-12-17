/* Some random stubs:
 * - NR_PROCS is normally instantiated during compilation
 * - minix_panic is removed
 * - locks and unlocks are removed
 * - timer stuff is removed
 * - debug-code is removed
 */
#define NR_PROCS 100
#define minix_panic(M, N) 
#define lock
#define unlock
#define get_uptime() 0
#define set_timer(a,b,c) 
typedef unsigned reg_t;         /* machine register */
typedef int proc_nr_t;      /* process table entry number */
typedef short sys_id_t;     /* system process index */
typedef int timer_t;
typedef int clock_t;
#define DEBUG_SCHED_CHECK 0
#define DEBUG             0

/* taken from /include/minix/com.h */
#define IDLE             -4 /* runs when no one else can run */
#define CLOCK      -3 /* alarms and other clock functions */
#define SYSTEM           -2 /* request system functionality */
#define KERNEL           -1 /* pseudo-process for IPC and scheduling */
#define HARDWARE     KERNEL /* for hardware interrupt handlers */
#define NR_TASKS    4 

/* taken from /include/minix/const.h */
#define EXTERN        /*extern ALBERT:We need to actually declare the variables...*/  /* used in *.h files */
#define PRIVATE       static  /* PRIVATE x limits the scope of x */
#define PUBLIC          /* PUBLIC is the opposite of PRIVATE */
#define TRUE               1  /* used for turning integers into Booleans */
#define FALSE              0  /* used for turning integers into Booleans */
#define PREEMPTIBLE     0x02    /* kernel tasks are not preemptible */
#define BILLABLE        0x04    /* some processes are not billable */
#define MAX(a, b)   ((a) > (b) ? (a) : (b))

/**
 * Stub from: /kernel/priv.h:112-27
 */
struct priv {
  sys_id_t s_id;    /* index of this system structure */
  short s_flags;    /* PREEMTIBLE, BILLABLE, etc. */
  reg_t *s_stack_guard;   /* stack guard word for kernel tasks */
};
#define STACK_GUARD ((reg_t) (sizeof(reg_t) == 2 ? 0xBEEF : 0xDEADBEEF))
#define BEG_PRIV_ADDR (&priv[0])
#define END_PRIV_ADDR (&priv[NR_SYS_PROCS])
#define priv_addr(i)      (ppriv_addr)[(i)]
#define priv_id(rp)   ((rp)->p_priv->s_id)
#define priv(rp)    ((rp)->p_priv)

/* Stub from /kernel/proc.h:16 */
struct proc {
  proc_nr_t p_nr;   /* number of this process (for fast access) */
  struct priv *p_priv;    /* system privileges structure */
  short p_rts_flags;    /* process is runnable only if zero */
  short p_misc_flags;   /* flags that do not suspend the process */

  char p_priority;    /* current scheduling priority */
  char p_max_priority;    /* maximum scheduling priority */
  char p_ticks_left;    /* number of scheduling ticks left */
  char p_quantum_size;    /* quantum size in ticks */

  struct proc *p_nextready; /* pointer to next ready process */
  struct proc *p_caller_q;  /* head of list of procs wishing to send */
  struct proc *p_q_link;  /* link to next proc wishing to send */
};

/* taken from kernel/glo.h:32-35 */
EXTERN struct proc *prev_ptr; /* previously running process */
EXTERN struct proc *proc_ptr; /* pointer to currently running process */
EXTERN struct proc *next_ptr; /* next process to run after restart() */
EXTERN struct proc *bill_ptr; /* process to bill for clock ticks */

/**
 * FROM: /kernel/proc.h
 * LINE: 112
 * TO:   146
 */

/* Bits for the runtime flags. A process is runnable iff p_rts_flags == 0. */
#define SLOT_FREE 0x01  /* process slot is free */
#define NO_PRIORITY     0x02  /* process has been stopped */
#define SENDING   0x04  /* process blocked trying to send */
#define RECEIVING 0x08  /* process blocked trying to receive */
#define SIGNALED  0x10  /* set when new kernel signal arrives */
#define SIG_PENDING 0x20  /* unready while signal being processed */
#define P_STOP    0x40  /* set when process is being traced */
#define NO_PRIV   0x80  /* keep forked system process from running */
#define NO_ENDPOINT    0x100  /* process cannot send or receive messages */
#define VMINHIBIT      0x200  /* not scheduled until pagetable set by VM */
#define PAGEFAULT      0x400  /* process has unhandled pagefault */
#define VMREQUEST      0x800  /* originator of vm memory request */

/* These runtime flags can be tested and manipulated by these macros. */

#define RTS_ISSET(rp, f) (((rp)->p_rts_flags & (f)) == (f))

/* Set flag and dequeue if the process was runnable. */
#define RTS_SET(rp, f)              \
  do {                \
    if(!(rp)->p_rts_flags) { dequeue(rp); }     \
    (rp)->p_rts_flags |=  (f);        \
  } while(0)

/* Clear flag and enqueue if the process was not runnable but is now. */
#define RTS_UNSET(rp, f)            \
  do {                \
    int rts;            \
    rts = (rp)->p_rts_flags;          \
    (rp)->p_rts_flags &= ~(f);        \
    if(rts && !(rp)->p_rts_flags) { enqueue(rp); }    \
  } while(0)

/**
 * FROM: /kernel/proc.h
 * LINE: 176
 * TO:   216
 */

/* Scheduling priorities for p_priority. Values must start at zero (highest
 * priority) and increment.  Priorities of the processes in the boot image 
 * can be set in table.c. IDLE must have a queue for itself, to prevent low 
 * priority user processes to run round-robin with IDLE. 
 */
#define NR_SCHED_QUEUES   16  /* MUST equal minimum priority + 1 */
#define TASK_Q       0  /* highest, used for kernel tasks */
#define MAX_USER_Q       0    /* highest priority for user processes */   
#define USER_Q       7    /* default (should correspond to nice 0) */   
#define MIN_USER_Q    14  /* minimum priority for user processes */
#define IDLE_Q      15    /* lowest, only IDLE process goes here */

/* Magic process table addresses. */
#define BEG_PROC_ADDR (&proc[0])
#define BEG_USER_ADDR (&proc[NR_TASKS])
#define END_PROC_ADDR (&proc[NR_TASKS + NR_PROCS])

#define NIL_PROC          ((struct proc *) 0)   
#define NIL_SYS_PROC      ((struct proc *) 1)   
#define cproc_addr(n)     (&(proc + NR_TASKS)[(n)])
#define proc_addr(n)      (pproc_addr + NR_TASKS)[(n)]
#define proc_nr(p)    ((p)->p_nr)

#define isokprocn(n)      ((unsigned) ((n) + NR_TASKS) < NR_PROCS + NR_TASKS)
#define isemptyn(n)       isemptyp(proc_addr(n)) 
#define isemptyp(p)       ((p)->p_rts_flags == SLOT_FREE)
#define iskernelp(p)    iskerneln((p)->p_nr)
#define iskerneln(n)    ((n) < 0)
#define isuserp(p)        isusern((p)->p_nr)
#define isusern(n)        ((n) >= 0)

/* The process table and pointers to process table slots. The pointers allow
 * faster access because now a process entry can be found by indexing the
 * pproc_addr array, while accessing an element i requires a multiplication
 * with sizeof(struct proc) to determine the address. 
 */
EXTERN struct proc proc[NR_TASKS + NR_PROCS]; /* process table */
EXTERN struct proc *pproc_addr[NR_TASKS + NR_PROCS];
EXTERN struct proc *rdy_head[NR_SCHED_QUEUES]; /* ptrs to ready list headers */
EXTERN struct proc *rdy_tail[NR_SCHED_QUEUES]; /* ptrs to ready list tails */

/**
 * FROM: /kernel/proc.c
 * LINE: 1106
 * TO:   1314
 */
static void sched (struct proc *rp, int *queue, int *front);
static void pick_proc (void);

/*===========================================================================*
 *        enqueue              * 
 *===========================================================================*/

PUBLIC void enqueue(rp)
register struct proc *rp; /* this process is now runnable */
{
/* Add 'rp' to one of the queues of runnable processes.  This function is 
 * responsible for inserting a process into one of the scheduling queues. 
 * The mechanism is implemented here.   The actual scheduling policy is
 * defined in sched() and pick_proc().
 */
  int q;          /* scheduling queue to use */
  int front;          /* add to front or back */

#if DEBUG_SCHED_CHECK
  if(!intr_disabled()) { minix_panic("enqueue with interrupts enabled", NO_NUM); }
  CHECK_RUNQUEUES;
  if (rp->p_ready) minix_panic("enqueue already ready process", NO_NUM);
#endif

  /* Determine where to insert to process. */
  sched(rp, &q, &front);

  /* Now add the process to the queue. */
  if (rdy_head[q] == NIL_PROC) {    /* add to empty queue */
      rdy_head[q] = rdy_tail[q] = rp;     /* create a new queue */
      rp->p_nextready = NIL_PROC;   /* mark new end */
  }
  else if (front) {       /* add to head of queue */
      rp->p_nextready = rdy_head[q];    /* chain head of queue */
      rdy_head[q] = rp;       /* set new queue head */
  }
  else {          /* add to tail of queue */
      rdy_tail[q]->p_nextready = rp;    /* chain tail of queue */
      rdy_tail[q] = rp;       /* set new queue tail */
      rp->p_nextready = NIL_PROC;   /* mark new end */
  }

  /* Now select the next process to run, if there isn't a current
   * process yet or current process isn't ready any more, or
   * it's PREEMPTIBLE.
   */
  if(!proc_ptr || proc_ptr->p_rts_flags ||
    (priv(proc_ptr)->s_flags & PREEMPTIBLE)) {
     pick_proc();
  }

#if DEBUG_SCHED_CHECK
  rp->p_ready = 1;
  CHECK_RUNQUEUES;
#endif
}

/*===========================================================================*
 *        dequeue              * 
 *===========================================================================*/
PUBLIC void dequeue(rp)
register struct proc *rp; /* this process is no longer runnable */
{
/* A process must be removed from the scheduling queues, for example, because
 * it has blocked.  If the currently active process is removed, a new process
 * is picked to run by calling pick_proc().
 */
  register int q = rp->p_priority;    /* queue to use */
  register struct proc **xpp;     /* iterate over queue */
  register struct proc *prev_xp;

  /* Side-effect for kernel: check if the task's stack still is ok? */
  if (iskernelp(rp)) {
  if (*priv(rp)->s_stack_guard != STACK_GUARD)
    minix_panic("stack overrun by task", proc_nr(rp));
  }

#if DEBUG_SCHED_CHECK
  CHECK_RUNQUEUES;
  if(!intr_disabled()) { minix_panic("dequeue with interrupts enabled", NO_NUM); }
  if (! rp->p_ready) minix_panic("dequeue() already unready process", NO_NUM);
#endif
  /* Now make sure that the process is not in its ready queue. Remove the 
   * process if it is found. A process can be made unready even if it is not 
   * running by being sent a signal that kills it.
   */
  prev_xp = NIL_PROC;
  for (xpp = &rdy_head[q]; *xpp != NIL_PROC; xpp = &(*xpp)->p_nextready) {

      if (*xpp == rp) {       /* found process to remove */
          *xpp = (*xpp)->p_nextready;   /* replace with next chain */
          if (rp == rdy_tail[q])    /* queue tail removed */
              rdy_tail[q] = prev_xp;    /* set new tail */
          if (rp == proc_ptr || rp == next_ptr) /* active process removed */
              pick_proc();      /* pick new process to run */
          break;
      }
      prev_xp = *xpp;       /* save previous in chain */
  }

#if DEBUG_SCHED_CHECK
  rp->p_ready = 0;
  CHECK_RUNQUEUES;
#endif
}

/*===========================================================================*
 *        sched              * 
 *===========================================================================*/
PRIVATE void sched(rp, queue, front)
register struct proc *rp;     /* process to be scheduled */
int *queue;         /* return: queue to use */
int *front;         /* return: front or back */
{
/* This function determines the scheduling policy.  It is called whenever a
 * process must be added to one of the scheduling queues to decide where to
 * insert it.  As a side-effect the process' priority may be updated.  
 */
  int time_left = (rp->p_ticks_left > 0); /* quantum fully consumed */

  /* Check whether the process has time left. Otherwise give a new quantum 
   * and lower the process' priority, unless the process already is in the 
   * lowest queue.  
   */
  if (! time_left) {        /* quantum consumed ? */
      rp->p_ticks_left = rp->p_quantum_size;  /* give new quantum */
      if (rp->p_priority < (IDLE_Q-1)) {
          rp->p_priority += 1;      /* lower priority */
      }
  }

  /* If there is time left, the process is added to the front of its queue, 
   * so that it can immediately run. The queue to use simply is always the
   * process' current priority. 
   */
  *queue = rp->p_priority;
  *front = time_left;
}

/*===========================================================================*
 *        pick_proc                                                          * 
 *===========================================================================*/


/*
Using \length(rdy_head) guves the error: unbound function \length
*/
/*@ requires \valid(rdy_head + (0.. (NR_SCHED_QUEUES-1))) && rdy_head[0] != NIL_PROC;
  @ assigns *next_ptr, *bill_ptr; 
  @ ensures \valid(next_ptr) || (\valid(next_ptr) && \valid(bill_ptr));
  @*/
PRIVATE void pick_proc()
{
/* Decide who to run now.  A new process is selected by setting 'next_ptr'.
 * When a billable process is selected, record it in 'bill_ptr', so that the 
 * clock task can tell who to bill for system time.
 */
  register struct proc *rp;     /* process to run */
  int q;                        /* iterate over queues */

  /* Check each of the scheduling queues for ready processes. The number of
   * queues is defined in proc.h, and priorities are set in the task table.
   * The lowest queue contains IDLE, which is always ready.
   */

  /*@ loop pragma UNROLL 17; */
  for (q=0; q < NR_SCHED_QUEUES; q++) {
      if ( (rp = rdy_head[q]) != NIL_PROC) {
          next_ptr = rp;        /* run process 'rp' next */
#if 0
    if(rp->p_endpoint != 4 && rp->p_endpoint != 5 && rp->p_endpoint != IDLE && rp->p_endpoint != SYSTEM)
      kprintf("[run %s]",  rp->p_name);
#endif
          /*@ requires \valid(rp->p_priv); 
            @ ensures \valid(bill_ptr);
            */
          if (priv(rp)->s_flags & BILLABLE) {
              bill_ptr = rp;      /* bill for system time */
          }
          return;
      }
  }
  
  /* ALBERT
  minix_panic("no ready process", NO_NUM);
  */
}

/*===========================================================================*
 *        balance_queues             *
 *===========================================================================*/
#define Q_BALANCE_TICKS  100

// proc[NR_TASKS + NR_PROCS];
// NR_TASKS=4 , NR_PROCS=100
/*@ requires \valid(tp);
  @ requires \valid(proc + (0..104-1));
  @*/
PUBLIC void balance_queues(tp)
timer_t *tp;          /* watchdog timer pointer */
{
/* Check entire process table and give all process a higher priority. This
 * effectively means giving a new quantum. If a process already is at its 
 * maximum priority, its quantum will be renewed.
 */
  static timer_t queue_timer;     /* timer structure to use */
  register struct proc* rp;     /* process table pointer  */
  clock_t next_period;        /* time of next period  */
  int ticks_added = 0;        /* total time added */

  /*@ loop invariant rp < (BEG_PROC_ADDR+104); */
  for (rp=BEG_PROC_ADDR; rp<END_PROC_ADDR; rp++) {
      if (! isemptyp(rp)) {       /* check slot use */
     lock;
    if (rp->p_priority > rp->p_max_priority) {  /* update priority? */
        if (rp->p_rts_flags == 0) dequeue(rp);  /* take off queue */
        ticks_added += rp->p_quantum_size;  /* do accounting */
        rp->p_priority -= 1;      /* raise priority */
        if (rp->p_rts_flags == 0) enqueue(rp);  /* put on queue */
    }
    else {
        ticks_added += rp->p_quantum_size - rp->p_ticks_left;
              rp->p_ticks_left = rp->p_quantum_size;  /* give new quantum */
    }
    unlock;
      }
  }
#if DEBUG
  kprintf("ticks_added: %d\n", ticks_added);
#endif

  /* Now schedule a new watchdog timer to balance the queues again.  The 
   * period depends on the total amount of quantum ticks added.
   */
  next_period = MAX(Q_BALANCE_TICKS, ticks_added);
  set_timer(&queue_timer, get_uptime() + next_period, balance_queues);
}

int main() {
  balance_queues(0);
  return 0;
}
