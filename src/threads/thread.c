#include "threads/thread.h"
#include <debug.h>
#include <stddef.h>
#include <random.h>
#include <stdio.h>
#include <string.h>
#include "threads/flags.h"
#include "threads/interrupt.h"
#include "threads/intr-stubs.h"
#include "threads/palloc.h"
#include "threads/switch.h"
#include "threads/synch.h"
#include "threads/vaddr.h"
#include "devices/timer.h"
#include "threads/fixed-point.h"
#ifdef USERPROG
#include "userprog/process.h"
#endif

/* Random value for struct thread's `magic' member.
 Used to detect stack overflow.  See the big comment at the top
 of thread.h for details. */
#define THREAD_MAGIC 0xcd6abf4b

/* List of processes in THREAD_READY state, that is, processes
 that are ready to run but not actually running. */
static struct list ready_list;

/*List of processes in Sleep queue.
 */
static struct list sleep_list;
//Till Here

/* List of all processes.  Processes are added to this list
 when they are first scheduled and removed when they exit. */
static struct list all_list;

/* Idle thread. */
static struct thread *idle_thread;

/* Initial thread, the thread running init.c:main(). */
static struct thread *initial_thread;

/* Lock used by allocate_tid(). */
static struct lock tid_lock;

static int load_avg = 0;

/* Stack frame for kernel_thread(). */
struct kernel_thread_frame {
	void *eip; /* Return address. */
	thread_func *function; /* Function to call. */
	void *aux; /* Auxiliary data for function. */
};

/* Statistics. */
static long long idle_ticks; /* # of timer ticks spent idle. */
static long long kernel_ticks; /* # of timer ticks in kernel threads. */
static long long user_ticks; /* # of timer ticks in user programs. */

/* Scheduling. */
#define TIME_SLICE 4            /* # of timer ticks to give each thread. */
static unsigned thread_ticks; /* # of timer ticks since last yield. */

/* If false (default), use round-robin scheduler.
 If true, use multi-level feedback queue scheduler.
 Controlled by kernel command-line option "-o mlfqs". */
bool thread_mlfqs;

static struct list mlfq[64];

static void kernel_thread(thread_func *, void *aux);

static void idle(void *aux UNUSED);
static struct thread *running_thread(void);
static struct thread *next_thread_to_run(void);
static void init_thread(struct thread *, const char *name, int priority);
static bool is_thread(struct thread *) UNUSED;
static void *alloc_frame(struct thread *, size_t size);
static void schedule(void);
void thread_schedule_tail(struct thread *prev);
static tid_t allocate_tid(void);

/* Initializes the threading system by transforming the code
 that's currently running into a thread.  This can't work in
 general and it is possible in this case only because loader.S
 was careful to put the bottom of the stack at a page boundary.

 Also initializes the run queue and the tid lock.

 After calling this function, be sure to initialize the page
 allocator before trying to create any threads with
 thread_create().

 It is not safe to call thread_current() until this function
 finishes. */
void thread_init(void) {
	ASSERT(intr_get_level() == INTR_OFF);
	int i = 0;
	lock_init(&tid_lock);
	list_init(&ready_list);
	list_init(&sleep_list);
	list_init(&all_list);

	if (thread_mlfqs) {
		for (i = 0; i < 64; i++) {
			list_init(&mlfq[i]);
		}
	}

	/* Set up a thread structure for the running thread. */
	initial_thread = running_thread();
	init_thread(initial_thread, "main", PRI_DEFAULT);
	initial_thread->status = THREAD_RUNNING;
	initial_thread->tid = allocate_tid();
}

/* Starts preemptive thread scheduling by enabling interrupts.
 Also creates the idle thread. */
void thread_start(void) {
	/* Create the idle thread. */
	struct semaphore idle_started;
	sema_init(&idle_started, 0);
	thread_create("idle", PRI_MIN, idle, &idle_started);

	/* Start preemptive thread scheduling. */
	intr_enable();

	/* Wait for the idle thread to initialize idle_thread. */
	sema_down(&idle_started);
}

/* Called by the timer interrupt handler at each timer tick.
 Thus, this function runs in an external interrupt context. */
void thread_tick(void) {
	struct thread *t = thread_current();
	struct thread *sleepthread;
	struct list_elem *e;

	/* Update statistics. */
	if (t == idle_thread)
		idle_ticks++;
#ifdef USERPROG
	else if (t->pagedir != NULL)
	user_ticks++;
#endif
	else
		kernel_ticks++;

	/* update the recent cpu at every thread tick except idle thread*/
	if (thread_mlfqs && t != idle_thread) {
		t->recent_cpu += 100;
	}

	/*Decrement and check the sleep_tick value of all sleeping threads*/
	/*Wake up thread if sleep_tick reaches 0*/
	enum intr_level old_level;

	old_level = intr_disable();
	for (e = list_begin(&sleep_list); e != list_end(&sleep_list);
			e = list_next(e)) {
		sleepthread = list_entry(e, struct thread, elem);
		sleepthread->sleepwait--;
		if (!sleepthread->sleepwait)
			e = wakeup_thread(sleepthread);
	}
	intr_set_level(old_level);

	/*As we implemented Priority Scheduling, some optimization can be made while scheduling a new thread.
	 * No need to yield current running thread if its priority is highest and no other thread
	 * in ready queue has higher or equal priority to this thread. As yielding it will eventually
	 * schedule this higher priority thread again, with the extra overhead of context switch.
	 * High priority thread can only be yielded if there is one of the below event
	 * 1. Higher priority thread is created
	 * 2. Sleeping thread with higher priority got wake up.
	 * 3. Lock released which has a higher priority thread in its waiting list (same for semaphore)
	 * 4. Priority of a thread in ready queue changes and become higher then current thread
	 *    (either by thread_set_priority or as a result of recalculation of priority by mlfq scheduler)
	 */
	/* However, Enforce preemption if a same priority thread is present in ready queue to maintain a
	 * round robin scheduling between same priority threads */
	if (++thread_ticks >= TIME_SLICE) {
		if (t->priority == list_entry(list_begin(&ready_list), struct thread, elem)->priority)
			intr_yield_on_return();
		else
			thread_ticks = 0;
	}
}

/*Function to wake sleeping thread and put it back from sleep  list to ready list
 */
struct list_elem* wakeup_thread(struct thread *th)
{
	struct list_elem *prev;

	/*Need to return previous elem in sleep_list as th will point to another elem in ready queue after this function*/
	prev = th->elem.prev;
	list_remove(&th->elem);
	thread_unblock(th);

	/*Yield current thread if higher priority thread is wake up*/
	if (th->priority > thread_current()->priority)
		intr_yield_on_return();

	return prev;
}

/* Prints thread statistics. */
void thread_print_stats(void) {
	printf("Thread: %lld idle ticks, %lld kernel ticks, %lld user ticks\n",
			idle_ticks, kernel_ticks, user_ticks);
}

/* Creates a new kernel thread named NAME with the given initial
 PRIORITY, which executes FUNCTION passing AUX as the argument,
 and adds it to the ready queue.  Returns the thread identifier
 for the new thread, or TID_ERROR if creation fails.

 If thread_start() has been called, then the new thread may be
 scheduled before thread_create() returns.  It could even exit
 before thread_create() returns.  Contrariwise, the original
 thread may run for any amount of time before the new thread is
 scheduled.  Use a semaphore or some other form of
 synchronization if you need to ensure ordering.

 The code provided sets the new thread's `priority' member to
 PRIORITY, but no actual priority scheduling is implemented.
 Priority scheduling is the goal of Problem 1-3. */
tid_t thread_create(const char *name, int priority, thread_func *function,
		void *aux) {
	struct thread *t;
	struct kernel_thread_frame *kf;
	struct switch_entry_frame *ef;
	struct switch_threads_frame *sf;
	struct thread *cur;
	tid_t tid;
	enum intr_level old_level;

	ASSERT(function != NULL);

	/* Allocate thread. */
	t = palloc_get_page(PAL_ZERO);
	if (t == NULL)
		return TID_ERROR;

	init_thread(t, name, priority);
	tid = t->tid = allocate_tid();
	cur = thread_current();
	if (thread_mlfqs) {
		t->nice_value = cur->nice_value;
		t->recent_cpu = cur->recent_cpu;
	}
	/* Prepare thread for first run by initializing its stack.
	 Do this atomically so intermediate values for the 'stack'
	 member cannot be observed. */
	old_level = intr_disable();

	/* Stack frame for kernel_thread(). */
	kf = alloc_frame(t, sizeof *kf);
	kf->eip = NULL;
	kf->function = function;
	kf->aux = aux;

	/* Stack frame for switch_entry(). */
	ef = alloc_frame(t, sizeof *ef);
	ef->eip = (void (*)(void)) kernel_thread;

	/* Stack frame for switch_threads(). */
	sf = alloc_frame(t, sizeof *sf);
	sf->eip = switch_entry;
	sf->ebp = 0;

	intr_set_level(old_level);
	/* Add to run queue. */
	thread_unblock(t);

	if (t->priority > cur->priority)
		thread_yield();

	return tid;
}

/* Puts the current thread to sleep.  It will not be scheduled
 again until awoken by thread_unblock().

 This function must be called with interrupts turned off.  It
 is usually a better idea to use one of the synchronization
 primitives in synch.h. */
void thread_block(void) {
	ASSERT(!intr_context());
	ASSERT(intr_get_level() == INTR_OFF);

	thread_current()->status = THREAD_BLOCKED;
	schedule();
}

/* Transitions a blocked thread T to the ready-to-run state.
 This is an error if T is not blocked.  (Use thread_yield() to
 make the running thread ready.)

 This function does not preempt the running thread.  This can
 be important: if the caller had disabled interrupts itself,
 it may expect that it can atomically unblock a thread and
 update other data. */
void thread_unblock(struct thread *t) {
	enum intr_level old_level;

	ASSERT(is_thread(t));

	old_level = intr_disable();
	ASSERT(t->status == THREAD_BLOCKED);
	//list_push_back (&ready_list, &t->elem);
	/* based on the kernel option selected add the thread to MLFQ or priority queue*/
	if (thread_mlfqs) {

		int priority = 63 - (t->recent_cpu / 400) - (t->nice_value * 2);
		if (priority > 63) {
			priority = 63;
		}
		if (priority < 0) {
			priority = 0;
		}
		t->priority = priority;
		list_push_back(&mlfq[priority], &t->elem);
	} else {
		/*Push the thread at the position in ready queue according to priority*/
		priority_list_push(&ready_list, &t->elem, t->priority);
	}

	t->status = THREAD_READY;
	intr_set_level(old_level);
}

/*Push in the list according to priority*/
void priority_list_push(struct list *list, struct list_elem *elem, int priority) {
	struct list_elem *e;
	struct thread *t;

	if (list_empty(&ready_list))
		return list_push_back(list, elem);

	for (e = list_begin(list); e != list_end(list); e = list_next(e)) {
		t = list_entry(e, struct thread, elem);
		if (t->priority < priority)
			return list_insert(&t->elem, elem);

	}

	return list_push_back(list, elem);
}

/* Returns the name of the running thread. */
const char *
thread_name(void) {
	return thread_current()->name;
}

/* Returns the running thread.
 This is running_thread() plus a couple of sanity checks.
 See the big comment at the top of thread.h for details. */
struct thread *
thread_current(void) {
	struct thread *t = running_thread();

	/* Make sure T is really a thread.
	 If either of these assertions fire, then your thread may
	 have overflowed its stack.  Each thread has less than 4 kB
	 of stack, so a few big automatic arrays or moderate
	 recursion can cause stack overflow. */
	ASSERT(is_thread(t));
	ASSERT(t->status == THREAD_RUNNING);

	return t;
}

/* Returns the running thread's tid. */
tid_t thread_tid(void) {
	return thread_current()->tid;
}

/* Deschedules the current thread and destroys it.  Never
 returns to the caller. */
void thread_exit(void) {
	ASSERT(!intr_context());

#ifdef USERPROG
	process_exit ();
#endif

	/* Remove thread from all threads list, set our status to dying,
	 and schedule another process.  That process will destroy us
	 when it calls thread_schedule_tail(). */
	intr_disable();
	list_remove(&thread_current()->allelem);
	thread_current()->status = THREAD_DYING;
	schedule();
	NOT_REACHED ()
	;
}

/* Yields the CPU.  The current thread is not put to sleep and
 may be scheduled again immediately at the scheduler's whim. */
void thread_yield(void) {
	struct thread *cur = thread_current();
	enum intr_level old_level;
	int priority;
	ASSERT(!intr_context());

	old_level = intr_disable();
	if (cur != idle_thread) {
		/* add the thread to MLFQ */
		if (thread_mlfqs) {
			priority = PRI_MAX - (cur->recent_cpu / 400)
					- (cur->nice_value * 2);
			if (priority < 0) {
				priority = 0;
			} else if (priority > 63) {
				priority = 63;
			}
			list_push_back(&mlfq[priority], &cur->elem);
		} else {
			priority_list_push(&ready_list, &cur->elem, cur->priority);
		}
	}
	cur->status = THREAD_READY;
	schedule();
	intr_set_level(old_level);
}

/*yields the cpu, puts the thread to sleep and in sleep queue
 * and after timer ticks, puts the thread back to ready queue.
 */
void thread_yield_sleep(int64_t ticks) {

	struct thread *cur = thread_current();
	cur->sleepwait = ticks;
	enum intr_level old_level;


	old_level = intr_disable();

	list_push_back(&sleep_list, &cur->elem);
	thread_block();

	intr_set_level(old_level);

}

/* Invoke function 'func' on all threads, passing along 'aux'.
 This function must be called with interrupts off. */
void thread_foreach(thread_action_func *func, void *aux) {
	struct list_elem *e;

	ASSERT(intr_get_level() == INTR_OFF);

	for (e = list_begin(&all_list); e != list_end(&all_list);
			e = list_next(e)) {
		struct thread *t = list_entry(e, struct thread, allelem);
		func(t, aux);
	}
}

/* Sets the current thread's priority to NEW_PRIORITY. */
void thread_set_priority(int new_priority) {
	struct thread *t;
	if (thread_current()->priority == thread_current()->orig_priority) //Handle Case of priority donation
		thread_current()->priority = new_priority;
	thread_current()->orig_priority = new_priority;

	t = list_entry(list_begin(&ready_list), struct thread, elem);

	if (thread_current()->priority < t->priority)
		thread_yield();
}

/* Returns the current thread's priority. */
int thread_get_priority(void) {
	struct thread *t = thread_current();

	if (thread_mlfqs) {
		int priority = 63 - (t->recent_cpu / 400) - (t->nice_value * 2);
		if (priority > 63) {
			priority = 63;
		}
		if (priority < 0) {
			priority = 0;
		}
		t->priority = priority;

		return t->priority;
	} else
		return t->priority;
}

/* Sets the current thread's nice value to NICE.
 * Recalculate the thread priority and yield if it is not highest priority thread.
 *  */
void thread_set_nice(int nice UNUSED) {
	int priority;
	int i;
	struct thread *t = thread_current();
	t->nice_value = nice;

	priority = PRI_MAX - (t->recent_cpu / 400) - (t->nice_value * 2);

	if (priority < 0) {
		t->priority = 0;
	} else if (priority > 63) {
		t->priority = 63;
	} else {
		t->priority = priority;
	}

	if (thread_mlfqs) {
		for (i = 63; i >= 0; i--) {
			if (!list_empty(&mlfq[i])) {
				break;
			}
		}
		if (i > t->priority) {
			thread_yield();
		}
	}

}

/* Returns the current thread's nice value. */
int thread_get_nice(void) {
	return thread_current()->nice_value;
}

/* Returns 100 times the system load average. */
int thread_get_load_avg(void) {
	return load_avg / 100;
}

/**
 * Calculate the systems load at each TIMER_FREQ interval
 * update the load avg of the system every TIMER_FREQ
 *
 * load_avg = (59/60)*load_avg + (1/60)*ready_threads.
 */
void update_load_avg() {
	int ready_t = no_of_ready_threads();
	int temp1 = 0;
	int temp2 = 0;
	int temp3 = 0;
	temp1 = fix_div(59, 60).v;
	temp2 = fix_mul(temp1, fix_div(load_avg, 10000).v).v;
	temp3 = fix_div(ready_t, 60).v;
	load_avg = fix_mul((temp2 + temp3), 10000).v;
}

/* Returns 100 times the current thread's recent_cpu value. */
int thread_get_recent_cpu(void) {
	return (thread_current()->recent_cpu);
}

/* update recent cpu time of every thread at TIMER_FREQ
 *
 * */
void update_recent_cpu() {
	int l_avg = thread_get_load_avg();

	struct list_elem *e;
	// (2*load_avg)/(2*load_avg + 1)
	int cof_recent_cpu;
	int l1 = 0;
	int l2 = 0;
	int r_cpu;
	// iterate over all the list and update recent cpu of all threads except idle thread.
	for (e = list_begin(&all_list); e != list_end(&all_list);
			e = list_next(e)) {
		struct thread *t = list_entry(e, struct thread, allelem);

		if (t != idle_thread) {
			r_cpu = t->recent_cpu;
			l1 = 2 * fix_div(l_avg, 100).v;
			l2 = l1 + FIX_F;

			cof_recent_cpu = fix_div(l1, l2).v;
			r_cpu = cof_recent_cpu * r_cpu;
			r_cpu = (r_cpu) / FIX_F;
			t->recent_cpu = (fix_div(r_cpu, 100).v + t->nice_value * FIX_F)
					* 100 / FIX_F;
		}
	}
}

/**
 * calculate the thread priority for every thread in MLFQ
 */
void calculate_threads_priority() {

	int priority_new, max_priority=0;
	struct list_elem *e;

	for (e = list_begin(&all_list); e != list_end(&all_list);
			e = list_next(e)) {
		struct thread *t = list_entry(e, struct thread, allelem);
		if (t != idle_thread) {
			priority_new = PRI_MAX - (t->recent_cpu / 400)
					- (t->nice_value * 2);
			t->priority = priority_new;

			if ((t != thread_current()) && (priority_new > max_priority))
				max_priority = priority_new;
		}
	}
	/*Yield current thread if a higher priority thread is in ready queue*/
	if (thread_current ()->priority < max_priority)
		intr_yield_on_return();
}

/**
 * number of threads that are either running or ready to run at time of update
 * (not including the idle thread).
 */
int no_of_ready_threads() {
	int current = 0;
	int ready = 0;
	int i;
	struct thread *t;
	t = thread_current();
	if (is_thread(t) && strcmp(t->name, "idle")) {
		current++;
	}

	for (i = 63; i >= 0; i--) {
		if (!list_empty(&mlfq[i])) {
			ready += list_size(&mlfq[i]);
		}
	}

	return current + ready;
}
/* Idle thread.  Executes when no other thread is ready to run.

 The idle thread is initially put on the ready list by
 thread_start().  It will be scheduled once initially, at which
 point it initializes idle_thread, "up"s the semaphore passed
 to it to enable thread_start() to continue, and immediately
 blocks.  After that, the idle thread never appears in the
 ready list.  It is returned by next_thread_to_run() as a
 special case when the ready list is empty. */
static void idle(void *idle_started_ UNUSED) {
	struct semaphore *idle_started = idle_started_;
	idle_thread = thread_current();
	sema_up(idle_started);

	for (;;) {
		/* Let someone else run. */
		intr_disable();
		thread_block();

		/* Re-enable interrupts and wait for the next one.

		 The `sti' instruction disables interrupts until the
		 completion of the next instruction, so these two
		 instructions are executed atomically.  This atomicity is
		 important; otherwise, an interrupt could be handled
		 between re-enabling interrupts and waiting for the next
		 one to occur, wasting as much as one clock tick worth of
		 time.

		 See [IA32-v2a] "HLT", [IA32-v2b] "STI", and [IA32-v3a]
		 7.11.1 "HLT Instruction". */
		asm volatile ("sti; hlt" : : : "memory");
	}
}

/* Function used as the basis for a kernel thread. */
static void kernel_thread(thread_func *function, void *aux) {
	ASSERT(function != NULL);

	intr_enable(); /* The scheduler runs with interrupts off. */
	function(aux); /* Execute the thread function. */
	thread_exit(); /* If function() returns, kill the thread. */
}

/* Returns the running thread. */
struct thread *
running_thread(void) {
	uint32_t *esp;

	/* Copy the CPU's stack pointer into `esp', and then round that
	 down to the start of a page.  Because `struct thread' is
	 always at the beginning of a page and the stack pointer is
	 somewhere in the middle, this locates the curent thread. */
	asm ("mov %%esp, %0" : "=g" (esp));
	return pg_round_down(esp);
}

/* Returns true if T appears to point to a valid thread. */
static bool is_thread(struct thread *t) {
	return t != NULL && t->magic == THREAD_MAGIC;
}

/* Does basic initialization of T as a blocked thread named
 NAME. */
static void init_thread(struct thread *t, const char *name, int priority) {
	ASSERT(t != NULL);
	ASSERT(PRI_MIN <= priority && priority <= PRI_MAX);
	ASSERT(name != NULL);

	memset(t, 0, sizeof *t);
	t->status = THREAD_BLOCKED;
	strlcpy(t->name, name, sizeof t->name);
	t->stack = (uint8_t *) t + PGSIZE;
	t->priority = priority;
	t->orig_priority = priority;
	t->acquiring_lock = NULL;
	t->acquiring_sema = NULL;
	t->magic = THREAD_MAGIC;
	list_push_back(&all_list, &t->allelem);
	list_init(&t->acquired_locks);
}

/* Allocates a SIZE-byte frame at the top of thread T's stack and
 returns a pointer to the frame's base. */
static void *
alloc_frame(struct thread *t, size_t size) {
	/* Stack data is always allocated in word-size units. */
	ASSERT(is_thread(t));
	ASSERT(size % sizeof(uint32_t) == 0);

	t->stack -= size;
	return t->stack;
}

/* Chooses and returns the next thread to be scheduled.  Should
 return a thread from the run queue, unless the run queue is
 empty.  (If the running thread can continue running, then it
 will be in the run queue.)  If the run queue is empty, return
 idle_thread. */
static struct thread *
next_thread_to_run(void) {
	int i = 0;

	// Chose highest priority thread from MLFQ
	if (thread_mlfqs) {
		for (i = 63; i >= 0; i--) {
			if (!list_empty(&mlfq[i])) {
				break;
			}
		}

		if (i + 1 == 0)
			return idle_thread;
		else {
			return list_entry(list_pop_front(&mlfq[i]), struct thread, elem);
		}

	} else {
		if (list_empty(&ready_list))
			return idle_thread;
		else
			return list_entry(list_pop_front(&ready_list), struct thread, elem);
	}

}

/* Completes a thread switch by activating the new thread's page
 tables, and, if the previous thread is dying, destroying it.

 At this function's invocation, we just switched from thread
 PREV, the new thread is already running, and interrupts are
 still disabled.  This function is normally invoked by
 thread_schedule() as its final action before returning, but
 the first time a thread is scheduled it is called by
 switch_entry() (see switch.S).

 It's not safe to call printf() until the thread switch is
 complete.  In practice that means that printf()s should be
 added at the end of the function.

 After this function and its caller returns, the thread switch
 is complete. */
void thread_schedule_tail(struct thread *prev) {
	struct thread *cur = running_thread();

	ASSERT(intr_get_level() == INTR_OFF);

	/* Mark us as running. */
	cur->status = THREAD_RUNNING;

	/* Start new time slice. */
	thread_ticks = 0;

#ifdef USERPROG
	/* Activate the new address space. */
	process_activate ();
#endif

	/* If the thread we switched from is dying, destroy its struct
	 thread.  This must happen late so that thread_exit() doesn't
	 pull out the rug under itself.  (We don't free
	 initial_thread because its memory was not obtained via
	 palloc().) */
	if (prev != NULL && prev->status == THREAD_DYING
			&& prev != initial_thread) {
		ASSERT(prev != cur);
		palloc_free_page(prev);
	}
}

/* Schedules a new process.  At entry, interrupts must be off and
 the running process's state must have been changed from
 running to some other state.  This function finds another
 thread to run and switches to it.

 It's not safe to call printf() until thread_schedule_tail()
 has completed. */
static void schedule(void) {
	struct thread *cur = running_thread();
	struct thread *next = next_thread_to_run();
	struct thread *prev = NULL;

	ASSERT(intr_get_level() == INTR_OFF);
	ASSERT(cur->status != THREAD_RUNNING);
	ASSERT(is_thread(next));
	//printf("curr thread %s next thread %s \n", cur->name, next->name);
	if (cur != next)
		prev = switch_threads(cur, next);
	thread_schedule_tail(prev);
}

/* Returns a tid to use for a new thread. */
static tid_t allocate_tid(void) {
	static tid_t next_tid = 1;
	tid_t tid;

	lock_acquire(&tid_lock);
	tid = next_tid++;
	lock_release(&tid_lock);

	return tid;
}

/* Offset of `stack' member within `struct thread'.
 Used by switch.S, which can't figure it out on its own. */
uint32_t thread_stack_ofs = offsetof(struct thread, stack);
