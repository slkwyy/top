/*
 * Copyright (c) 1984 through 2007, William LeFebvre
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 *     * Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 * 
 *     * Redistributions in binary form must reproduce the above
 * copyright notice, this list of conditions and the following disclaimer
 * in the documentation and/or other materials provided with the
 * distribution.
 * 
 *     * Neither the name of William LeFebvre nor the names of other
 * contributors may be used to endorse or promote products derived from
 * this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

/*
 * top - a top users display for Unix
 *
 * SYNOPSIS:  For FreeBSD-2.x, 3.x, 4.x, and 5.x
 *
 * DESCRIPTION:
 * Originally written for BSD4.4 system by Christos Zoulas.
 * Ported to FreeBSD 2.x by Steven Wallace && Wolfram Schneider
 * Order support hacked in from top-3.5beta6/machine/m_aix41.c
 *   by Monte Mitzelfelt
 * Ported to FreeBSD 5.x by William LeFebvre
 *
 * AUTHOR:  Christos Zoulas <christos@ee.cornell.edu>
 *          Steven Wallace  <swallace@freebsd.org>
 *          Wolfram Schneider <wosch@FreeBSD.org>
 */


#include <sys/time.h>
#include <sys/types.h>
#include <sys/signal.h>
#include <sys/param.h>

#include "config.h"
#include <stdio.h>
#include <string.h>
#include <nlist.h>
#include <math.h>
#include <kvm.h>
#include <pwd.h>
#include <sys/errno.h>
#include <sys/sysctl.h>
#include <sys/dkstat.h>
#include <sys/file.h>
#include <sys/time.h>
#include <sys/proc.h>
#include <sys/user.h>
#include <sys/vmmeter.h>
#include <sys/resource.h>
#include <sys/rtprio.h>
#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif

/* Swap */
#include <stdlib.h>
#include <sys/conf.h>

#include <osreldate.h> /* for changes in kernel structures */

#include "top.h"
#include "machine.h"
#include "utils.h"
#include "username.h"
#include "hash.h"

extern char* printable __P((char *));
int swapmode __P((int *retavail, int *retfree));
static int smpmode;
static int namelength;

/* Older OS versions can't show threads */
#if OSMAJOR >= 5
#define HAS_THREADS
#endif

/* get_process_info passes back a handle.  This is what it looks like: */

struct handle
{
    struct kinfo_proc **next_proc;	/* points to next valid proc pointer */
    int remaining;		/* number of pointers remaining */
};

/* declarations for load_avg */
#include "loadavg.h"

/* macros to access process information */
#if OSMAJOR <= 4
#define PP(pp, field) ((pp)->kp_proc . p_##field)
#define EP(pp, field) ((pp)->kp_eproc . e_##field)
#define VP(pp, field) ((pp)->kp_eproc.e_vm . vm_##field)
#define PRUID(pp) ((pp)->kp_eproc.e_pcred.p_ruid)
#else
#define PP(pp, field) ((pp)->ki_##field)
#define EP(pp, field) ((pp)->ki_##field)
#define VP(pp, field) ((pp)->ki_##field)
#define PRUID(pp) ((pp)->ki_ruid)
#define RP(pp, field) ((pp)->ki_rusage.ru_##field)
#define PPCPU(pp) ((pp)->ki_sparelongs[0])
#define SPPTR(pp) ((pp)->ki_spareptrs[0])
#define SP(pp, field) (((struct save_proc *)((pp)->ki_spareptrs[0]))->sp_##field)
#endif

/* what we consider to be process size: */
#if OSMAJOR <= 4
#define PROCSIZE(pp) (VP((pp), map.size) / 1024)
#else
#define PROCSIZE(pp) (((pp)->ki_size) / 1024)
#endif

/* definitions for indices in the nlist array */

static struct nlist nlst[] = {
#define X_CCPU		0
    { "_ccpu" },
#define X_CP_TIME	1
    { "_cp_time" },
#define X_AVENRUN	2
    { "_averunnable" },

#define X_BUFSPACE	3
	{ "_bufspace" },	/* K in buffer cache */

#define X_BOOTTIME	4
    { "_boottime" },

    { 0 }
};

/* calculate a per-second rate using milliseconds */
#define per_second(n, msec)   (((n) * 1000) / (msec))

/* define what weighted cpu is.  */
#define weighted_cpu(pct, pp) (PP((pp), swtime) == 0 ? 0.0 : \
			 ((pct) / (1.0 - exp(PP((pp), swtime) * logcpu))))

/* process state names for the "STATE" column of the display */
/* the extra nulls in the string "run" are for adding a slash and
   the processor number when needed */

char *state_abbrev[] =
{
    "", "START", "RUN", "SLEEP", "STOP", "ZOMB", "WAIT", "LOCK"
};


static kvm_t *kd;

/* values that we stash away in _init and use in later routines */

static double logcpu;

/* these are retrieved from the kernel in _init */

static load_avg  ccpu;

/* these are offsets obtained via nlist and used in the get_ functions */

static unsigned long cp_time_offset;
static unsigned long avenrun_offset;
static unsigned long bufspace_offset;

/* these are for dealing with sysctl-based data */
#define MAXMIBLEN 8
struct sysctl_mib {
    char *name;
    int mib[MAXMIBLEN];
    size_t miblen;
};
static struct sysctl_mib mibs[] = {
    { "vm.stats.sys.v_swtch" },
#define V_SWTCH 0
    { "vm.stats.sys.v_trap" },
#define V_TRAP 1
    { "vm.stats.sys.v_intr" },
#define V_INTR 2
    { "vm.stats.sys.v_soft" },
#define V_SOFT 3
    { "vm.stats.vm.v_forks" },
#define V_FORKS 4
    { "vm.stats.vm.v_vforks" },
#define V_VFORKS 5
    { "vm.stats.vm.v_rforks" },
#define V_RFORKS 6
    { "vm.stats.vm.v_vm_faults" },
#define V_VM_FAULTS 7
    { "vm.stats.vm.v_swapin" },
#define V_SWAPIN 8
    { "vm.stats.vm.v_swapout" },
#define V_SWAPOUT 9
    { "vm.stats.vm.v_tfree" },
#define V_TFREE 10
    { "vm.stats.vm.v_vnodein" },
#define V_VNODEIN 11
    { "vm.stats.vm.v_vnodeout" },
#define V_VNODEOUT 12
    { "vm.stats.vm.v_active_count" },
#define V_ACTIVE_COUNT 13
    { "vm.stats.vm.v_inactive_count" },
#define V_INACTIVE_COUNT 14
    { "vm.stats.vm.v_wire_count" },
#define V_WIRE_COUNT 15
    { "vm.stats.vm.v_cache_count" },
#define V_CACHE_COUNT 16
    { "vm.stats.vm.v_free_count" },
#define V_FREE_COUNT 17
    { "vm.stats.vm.v_swappgsin" },
#define V_SWAPPGSIN 18
    { "vm.stats.vm.v_swappgsout" },
#define V_SWAPPGSOUT 19
    { NULL }
};
    

/* these are for calculating cpu state percentages */

static long cp_time[CPUSTATES];
static long cp_old[CPUSTATES];
static long cp_diff[CPUSTATES];

/* these are for detailing the process states */

int process_states[6];
char *procstatenames[] = {
    "", " starting, ", " running, ", " sleeping, ", " stopped, ",
    " zombie, ",
    NULL
};

/* these are for detailing the cpu states */

int cpu_states[CPUSTATES];
char *cpustatenames[] = {
    "user", "nice", "system", "interrupt", "idle", NULL
};

/* these are for detailing the kernel information */

int kernel_stats[9];
char *kernelnames[] = {
    " ctxsw, ", " trap, ", " intr, ", " soft, ", " fork, ",
    " flt, ", " pgin, ", " pgout, ", " fr",
    NULL
};

/* these are for detailing the memory statistics */

long memory_stats[7];
char *memorynames[] = {
    "K Active, ", "K Inact, ", "K Wired, ", "K Cache, ", "K Buf, ", "K Free",
    NULL
};

long swap_stats[7];
char *swapnames[] = {
/*   0           1            2           3            4       5 */
    "K Total, ", "K Used, ", "K Free, ", "% Inuse, ", "K In, ", "K Out",
    NULL
};


/* these are for keeping track of the proc array */

static int nproc;
static int onproc = -1;
static int pref_len;
static struct kinfo_proc *pbase;
static struct kinfo_proc **pref;

/* this structure retains information from the proc array between samples */
struct save_proc {
    u_int64_t sp_runtime;
    long sp_vcsw;
    long sp_ivcsw;
    long sp_inblock;
    long sp_oublock;
    long sp_majflt;
    long sp_totalio;
    long sp_old_nvcsw;
    long sp_old_nivcsw;
    long sp_old_inblock;
    long sp_old_oublock;
    long sp_old_majflt;
};
hash_table *procs;

/* these are for getting the memory statistics */

static int pageshift;		/* log base 2 of the pagesize */

/* define pagetok in terms of pageshift */

#define pagetok(size) ((size) << pageshift)

/* useful externals */
long percentages();

/* sorting orders. first is default */
char *ordernames[] = {
    "cpu", "size", "res", "time", "pri", "io", NULL
};

/* compare routines */
int proc_compare(), compare_size(), compare_res(), compare_time(),
    compare_prio(), compare_io();

int (*proc_compares[])() = {
    proc_compare,
    compare_size,
    compare_res,
    compare_time,
    compare_prio,
    compare_io,
    NULL
};


/*
 * check_nlist(nlst) - checks the nlist to see if any symbols were not
 *		found.  For every symbol that was not found, a one-line
 *		message is printed to stderr.  The routine returns the
 *		number of symbols NOT found.
 */

static int
check_nlist(struct nlist *nlst)

{
    register int i;

    /* check to see if we got ALL the symbols we requested */
    /* this will write one line to stderr for every symbol not found */

    i = 0;
    while (nlst->n_name != NULL)
    {
	if (nlst->n_type == 0)
	{
	    /* this one wasn't found */
	    (void) fprintf(stderr, "kernel: no symbol named `%s'\n",
			   nlst->n_name);
	    i = 1;
	}
	dprintf("nlist %s: type %d, value %08x\n",
		nlst->n_name, nlst->n_type, nlst->n_value);
	nlst++;
    }

    return(i);
}


/*
 *  getkval(offset, ptr, size, refstr) - get a value out of the kernel.
 *	"offset" is the byte offset into the kernel for the desired value,
 *  	"ptr" points to a buffer into which the value is retrieved,
 *  	"size" is the size of the buffer (and the object to retrieve),
 *  	"refstr" is a reference string used when printing error meessages,
 *	    if "refstr" starts with a '!', then a failure on read will not
 *  	    be fatal (this may seem like a silly way to do things, but I
 *  	    really didn't want the overhead of another argument).
 *  	
 */

static int
getkval(unsigned long offset, int *ptr, int size, char *refstr)

{
    if (kvm_read(kd, offset, (char *) ptr, size) != size)
    {
	if (*refstr == '!')
	{
	    return(0);
	}
	else
	{
	    fprintf(stderr, "top: kvm_read for %s: %s\n",
		refstr, strerror(errno));
	    quit(23);
	}
    }
    return(1);
}

int
get_sysctl_mibs()

{
    struct sysctl_mib *mp;
    size_t len;

    mp = mibs;
    while (mp->name != NULL)
    {
	len = MAXMIBLEN;
	if (sysctlnametomib(mp->name, mp->mib, &len) == -1)
	{
	    perror("sysctlnametomib");
	    return -1;
	}
	mp->miblen = len;
	mp++;
    }
    return 0;
}

int
get_sysctl(int idx, void *v, size_t *vlen)

{
    int i;
    struct sysctl_mib *m;

    m = &(mibs[idx]);
    if ((i = sysctl(m->mib, m->miblen, v, vlen, NULL, 0)) == -1)
    {
	perror("sysctl");
    }
    return i;
}
    
int
machine_init(struct statics *statics)

{
    register int i = 0;
    register int pagesize;
    size_t len;

#ifdef notdef
    struct passwd *pw;
#endif /* notdef */
    struct timeval boottime;

    len = sizeof(smpmode);
    if ((sysctlbyname("machdep.smp_active", &smpmode, &len, NULL, 0) < 0 &&
         sysctlbyname("smp.smp_active", &smpmode, &len, NULL, 0) < 0) ||
	len != sizeof(smpmode))
    {
	smpmode = 0;
    }
    smpmode = smpmode != 0;

#ifdef notdef
    while ((pw = getpwent()) != NULL) {
	if (strlen(pw->pw_name) > namelength)
	    namelength = strlen(pw->pw_name);
    }
    if (namelength < 8)
	namelength = 8;
    if (smpmode && namelength > 13)
	namelength = 13;
    else if (namelength > 15)
	namelength = 15;
#endif

    if ((kd = kvm_open(NULL, NULL, NULL, O_RDONLY, "kvm_open")) == NULL)
	return -1;


    /* get the list of symbols we want to access in the kernel */
    i = kvm_nlist(kd, nlst);
    if (i == -1)
    {
	fprintf(stderr, "top: nlist failed\n");
	return(-1);
    }

    /* make sure they were all found */
    if (check_nlist(nlst) > 0)
    {
	return(-1);
    }

    /* get number of cpus */
    (void) getkval(nlst[X_CCPU].n_value, (int *)(&ccpu), sizeof(ccpu),
	    nlst[X_CCPU].n_name);

    /* get boot time */
    len = sizeof(boottime);
    if (sysctlbyname("kern.boottime", &boottime, &len, NULL, 0) == -1)
    {
	dprintf("machine_init: boottime fallback to getkval");
	(void) getkval(nlst[X_BOOTTIME].n_value, (int *)(&boottime),
		       sizeof(boottime), nlst[X_BOOTTIME].n_name);
    }

    /* stash away certain offsets for later use */
    cp_time_offset = nlst[X_CP_TIME].n_value;
    avenrun_offset = nlst[X_AVENRUN].n_value;
    bufspace_offset = nlst[X_BUFSPACE].n_value;

    /* this is used in calculating WCPU -- calculate it ahead of time */
    logcpu = log(loaddouble(ccpu));

    pbase = NULL;
    pref = NULL;
    nproc = 0;
    onproc = -1;
    /* get the page size with "getpagesize" and calculate pageshift from it */
    pagesize = getpagesize();
    pageshift = 0;
    while (pagesize > 1)
    {
	pageshift++;
	pagesize >>= 1;
    }

    /* translate sysctl paths to mibs for faster access */
    get_sysctl_mibs();

    /* create the hash table that remembers proc data */
    procs = hash_create(2039);

    /* we only need the amount of log(2)1024 for our conversion */
    pageshift -= LOG1024;

    /* fill in the statics information */
    statics->procstate_names = procstatenames;
    statics->cpustate_names = cpustatenames;
    statics->memory_names = memorynames;
    statics->kernel_names = kernelnames;
    statics->boottime = boottime.tv_sec;
    statics->swap_names = swapnames;
    statics->order_names = ordernames;
    statics->flags.fullcmds = 1;
    statics->flags.warmup = 1;
    statics->modemax = 2;
#ifdef HAS_THREADS
    statics->flags.threads = 1;
#endif

    /* all done! */
    return(0);
}

char *format_header(char *uname_field)

{
    return "";
}

static u_int ctxsws = 0;
static u_int traps = 0;
static u_int intrs = 0;
static u_int softs = 0;
static u_int64_t forks = 0;
static u_int pfaults;
static u_int pagein;
static u_int pageout;
static u_int tfreed;
static int swappgsin = -1;
static int swappgsout = -1;
extern struct timeval timeout;
static struct timeval lasttime = { 0, 0 };
static long elapsed_time;
static long elapsed_msecs;

void
get_vm_sum(struct vmmeter *sum)

{
    size_t len;

#define GET_VM_STAT(v, s)  len = sizeof(sum->s); \
get_sysctl(v, &(sum->s), &len)

    GET_VM_STAT(V_SWTCH, v_swtch);
    GET_VM_STAT(V_TRAP, v_trap);
    GET_VM_STAT(V_INTR, v_intr);
    GET_VM_STAT(V_SOFT, v_soft);
    GET_VM_STAT(V_VFORKS, v_vforks);
    GET_VM_STAT(V_FORKS, v_forks);
    GET_VM_STAT(V_RFORKS, v_rforks);
    GET_VM_STAT(V_VM_FAULTS, v_vm_faults);
    GET_VM_STAT(V_SWAPIN, v_swapin);
    GET_VM_STAT(V_SWAPOUT, v_swapout);
    GET_VM_STAT(V_TFREE, v_tfree);
    GET_VM_STAT(V_VNODEIN, v_vnodein);
    GET_VM_STAT(V_VNODEOUT, v_vnodeout);
    GET_VM_STAT(V_ACTIVE_COUNT, v_active_count);
    GET_VM_STAT(V_INACTIVE_COUNT, v_inactive_count);
    GET_VM_STAT(V_WIRE_COUNT, v_wire_count);
    GET_VM_STAT(V_CACHE_COUNT, v_cache_count);
    GET_VM_STAT(V_FREE_COUNT, v_free_count);
    GET_VM_STAT(V_SWAPPGSIN, v_swappgsin);
    GET_VM_STAT(V_SWAPPGSOUT, v_swappgsout);
}

void
get_system_info(struct system_info *si)

{
    long total;
    load_avg avenrun[3];
    struct timeval thistime;
    struct timeval timediff;

    /* timestamp and time difference */
    gettimeofday(&thistime, 0);
    timersub(&thistime, &lasttime, &timediff);
    elapsed_time = timediff.tv_sec * 1000000 + timediff.tv_usec;
    elapsed_msecs = timediff.tv_sec * 1000 + timediff.tv_usec / 1000;

    /* get the cp_time array */
    (void) getkval(cp_time_offset, (int *)cp_time, sizeof(cp_time),
		   nlst[X_CP_TIME].n_name);
    (void) getkval(avenrun_offset, (int *)avenrun, sizeof(avenrun),
		   nlst[X_AVENRUN].n_name);

    /* convert load averages to doubles */
    {
	register int i;
	register double *infoloadp;
	load_avg *avenrunp;

#ifdef notyet
	struct loadavg sysload;
	int size;
	getkerninfo(KINFO_LOADAVG, &sysload, &size, 0);
#endif

	infoloadp = si->load_avg;
	avenrunp = avenrun;
	for (i = 0; i < 3; i++)
	{
#ifdef notyet
	    *infoloadp++ = ((double) sysload.ldavg[i]) / sysload.fscale;
#endif
	    *infoloadp++ = loaddouble(*avenrunp++);
	}
    }

    /* convert cp_time counts to percentages */
    total = percentages(CPUSTATES, cpu_states, cp_time, cp_old, cp_diff);

    /* sum memory & swap statistics */
    {
	struct vmmeter sum;
	static unsigned int swap_delay = 0;
	static int swapavail = 0;
	static int swapfree = 0;
	static int bufspace = 0;

#ifdef notdef
        (void) getkval(cnt_offset, (int *)(&sum), sizeof(sum),
		   "_cnt");
#else
	get_vm_sum(&sum);
#endif
        (void) getkval(bufspace_offset, (int *)(&bufspace), sizeof(bufspace),
		   "_bufspace");

	/* kernel stats */
	dprintf("kernel: swtch %d, trap %d, intr %d, soft %d, vforks %d\n",
		sum.v_swtch, sum.v_trap, sum.v_intr, sum.v_soft, sum.v_vforks);
	kernel_stats[0] = per_second(sum.v_swtch - ctxsws, elapsed_msecs);
	kernel_stats[1] = per_second(sum.v_trap - traps, elapsed_msecs);
	kernel_stats[2] = per_second(sum.v_intr - intrs, elapsed_msecs);
	kernel_stats[3] = per_second(sum.v_soft - softs, elapsed_msecs);
	kernel_stats[4] = per_second(sum.v_vforks + sum.v_forks +
				     sum.v_rforks - forks, elapsed_msecs);
	kernel_stats[5] = per_second(sum.v_vm_faults - pfaults, elapsed_msecs);
	kernel_stats[6] = per_second(sum.v_swapin + sum.v_vnodein - pagein, elapsed_msecs);
	kernel_stats[7] = per_second(sum.v_swapout + sum.v_vnodeout - pageout, elapsed_msecs);
	kernel_stats[8] = per_second(sum.v_tfree - tfreed, elapsed_msecs);
	ctxsws = sum.v_swtch;
	traps = sum.v_trap;
	intrs = sum.v_intr;
	softs = sum.v_soft;
	forks = (u_int64_t)sum.v_vforks + sum.v_forks + sum.v_rforks;
	pfaults = sum.v_vm_faults;
	pagein = sum.v_swapin + sum.v_vnodein;
	pageout = sum.v_swapout + sum.v_vnodeout;
	tfreed = sum.v_tfree;

	/* convert memory stats to Kbytes */
	memory_stats[0] = pagetok(sum.v_active_count);
	memory_stats[1] = pagetok(sum.v_inactive_count);
	memory_stats[2] = pagetok(sum.v_wire_count);
	memory_stats[3] = pagetok(sum.v_cache_count);
	memory_stats[4] = bufspace / 1024;
	memory_stats[5] = pagetok(sum.v_free_count);
	memory_stats[6] = -1;

	/* first interval */
        if (swappgsin < 0) {
	    swap_stats[4] = 0;
	    swap_stats[5] = 0;
	} 

	/* compute differences between old and new swap statistic */
	else {
	    swap_stats[4] = pagetok(((sum.v_swappgsin - swappgsin)));
	    swap_stats[5] = pagetok(((sum.v_swappgsout - swappgsout)));
	}

        swappgsin = sum.v_swappgsin;
	swappgsout = sum.v_swappgsout;

	/* call CPU heavy swapmode() only for changes */
        if (swap_stats[4] > 0 || swap_stats[5] > 0 || swap_delay == 0) {
	    swap_stats[3] = swapmode(&swapavail, &swapfree);
	    swap_stats[0] = swapavail;
	    swap_stats[1] = swapavail - swapfree;
	    swap_stats[2] = swapfree;
	}
        swap_delay = 1;
	swap_stats[6] = -1;
    }

    /* set arrays and strings */
    si->cpustates = cpu_states;
    si->kernel = kernel_stats;
    si->memory = memory_stats;
    si->swap = swap_stats;

    si->last_pid = -1;

    lasttime = thistime;
}

static struct handle handle;
static int show_fullcmd;
static int show_usernames;
static int show_threads = 0;
static int display_mode;
static long total_io;


caddr_t
get_process_info(struct system_info *si,
			 struct process_select *sel,
			 int compare_index)

{
    register int i;
    register int total_procs;
    register int active_procs;
    register struct kinfo_proc **prefp;
    register struct kinfo_proc *pp;
    struct kinfo_proc *prev_pp = NULL;
    struct save_proc *savep;
    long proc_io;
    pid_t pid;
    int is_thread = 0;

    /* these are copied out of sel for speed */
    int show_idle;
    int show_self;
    int show_system;
    int show_uid;
    char *show_command;

    /* get all process information (threads, too) */
    nproc = 0;
    pbase = kvm_getprocs(kd, KERN_PROC_ALL, 0, &nproc);

    /* allocate space for stuff that holds proc related info */
    /* if realloc only grows space, then this test is unnecessary */
    if (nproc > onproc)
    {
	pref = (struct kinfo_proc **) realloc(pref,
					      sizeof(struct kinfo_proc *)
					      * (onproc = nproc));
    }

    /* make sure we got the space we asked for */
    if (pref == NULL || pbase == NULL)
    {
	(void) fprintf(stderr, "Out of memory.\n");
	quit(23);
    }
    /* get a pointer to the states summary array */
    si->procstates = process_states;

    /* set up flags which define what we are going to select */
    show_idle = sel->idle;
    show_self = 0;
    show_system = sel->system;
    show_uid = sel->uid != -1;
    show_fullcmd = sel->fullcmd;
    show_command = sel->command;
    show_usernames = sel->usernames;
    display_mode = sel->mode;
#ifdef HAS_THREADS
    show_threads = sel->threads;
#endif

    /* count up process states and get pointers to interesting procs */
    total_procs = 0;
    active_procs = 0;
    total_io = 0;
    memset((char *)process_states, 0, sizeof(process_states));
    prefp = pref;
    for (pp = pbase, i = 0; i < nproc; pp++, i++)
    {
	/*
	 *  Place pointers to each valid proc structure in pref[].
	 *  Process slots that are actually in use have a non-zero
	 *  status field.  Processes with P_SYSTEM set are system
	 *  processes---these get ignored unless show_sysprocs is set.
	 */
	pid = PP(pp, pid);
	if (PP(pp, stat) != 0 &&
	    (show_system || ((PP(pp, flag) & P_SYSTEM) == 0)))
	{
#ifdef HAS_THREADS
	    /* is this just a thread? */
	    is_thread = (prev_pp != NULL && PP(prev_pp, pid) == pid);

	    /* count this process and its state */
	    /* only count threads if we are showing them */
	    if (show_threads || !is_thread)
	    {
		total_procs++;
		process_states[(unsigned char) PP(pp, stat)]++;
	    }
#else /* !HAS_THREADS */
	    total_procs++;
	    process_states[(unsigned char) PP(pp, stat)]++;
#endif

	    /* grab old data from hash */
	    if ((savep = hash_lookup_pid(procs, pid)) == NULL)
	    {
		/* havent seen this one before */
		savep = (struct save_proc *)calloc(1, sizeof(struct save_proc));
		hash_add_pid(procs, pid, savep);
	    }

	    /* save the pointer to the sp struct */
	    SPPTR(pp) = (void *)savep;

	    /* calculate %cpu */
	    PPCPU(pp) = ((PP(pp, runtime) - savep->sp_runtime) * 10000) /
		elapsed_time;
	    dprintf("%d: runtime %lld, saved_runtime %lld, elapsed_time %d, ppcpu %d\n",
		    pid, PP(pp, runtime), savep->sp_runtime,
		    elapsed_time, PPCPU(pp));

	    /* calculate io differences */
	    proc_io = 0;
	    savep->sp_vcsw = (RP(pp, nvcsw) - savep->sp_old_nvcsw);
	    savep->sp_ivcsw = (RP(pp, nivcsw) - savep->sp_old_nivcsw);
	    proc_io += (savep->sp_inblock = (RP(pp, inblock) - savep->sp_old_inblock));
	    proc_io += (savep->sp_oublock = (RP(pp, oublock) - savep->sp_old_oublock));
	    proc_io += (savep->sp_majflt = (RP(pp, majflt) - savep->sp_old_majflt));
	    total_io += proc_io;
	    savep->sp_totalio = proc_io;

	    /* save data for next time */
	    savep->sp_runtime = PP(pp, runtime);
	    savep->sp_old_nvcsw = RP(pp, nvcsw);
	    savep->sp_old_nivcsw = RP(pp, nivcsw);
	    savep->sp_old_inblock = RP(pp, inblock);
	    savep->sp_old_oublock = RP(pp, oublock);
	    savep->sp_old_majflt = RP(pp, majflt);

	    /* is this one selected for viewing? */
	    if ((PP(pp, stat) != SZOMB) &&
		(show_idle || (PP(pp, pctcpu) != 0) || 
		 (PP(pp, stat) == SRUN)) &&
		(!show_uid || PRUID(pp) == (uid_t)sel->uid) &&
		(show_command == NULL ||
		 strcasestr(PP(pp, comm), show_command) != NULL))
	    {
#ifdef HAS_THREADS
		/* yes, but make sure it isn't just a thread */
		if (show_threads || !is_thread)
		{
		    /* we will be showing this process */
		    *prefp++ = pp;
		    active_procs++;
		    prev_pp = pp;
		}
		else
		{
		    PP(prev_pp, pctcpu) += PP(pp, pctcpu);
		}
#else /* !HAS_THREADS */
		/* we will be showing this process */
		*prefp++ = pp;
		active_procs++;
		prev_pp = pp;
#endif
	    }
	}
    }

    dprintf("total_io: %d\n", total_io);
    if (total_io == 0) total_io = 1;

    /* if requested, sort the "interesting" processes */
    qsort((char *)pref, active_procs, sizeof(struct kinfo_proc *),
	  proc_compares[compare_index]);

    /* remember active and total counts */
    si->p_total = total_procs;
    si->p_active = pref_len = active_procs;

    /* pass back a handle */
    handle.next_proc = pref;
    handle.remaining = active_procs;
    return((caddr_t)&handle);
}

/*
 * Every header starts with "PID" followed by either "USERNAME" or "UID",
 * depending on sel->usernames.  After that, one of the following 5
 * headers can be used.  The exact header depends on display_mode, 
 * smpmode, and sel->threads.
 */

static char *proc_header[] = {
    "THR PRI NICE  SIZE    RES STATE    TIME    CPU COMMAND",
    "THR PRI NICE  SIZE    RES STATE  C   TIME    CPU COMMAND",
    "PRI NICE  SIZE    RES STATE    TIME   WCPU    CPU COMMAND",
    "PRI NICE  SIZE    RES STATE  C   TIME   WCPU    CPU COMMAND",
    "  VCSW  IVCSW   READ  WRITE  FAULT  TOTAL PERCENT COMMAND"
};

static char p_header[MAX_COLS];

char *
format_process_header(struct process_select *sel, caddr_t handle, int count)

{
    char *h;
    char *p;
    struct kinfo_proc **kip;
    int n;
    int w;

    /* h is the proper header format to use */
    if (display_mode == 1)
    {
	h = proc_header[4];
    }
    else
    {
#ifdef HAS_THREADS
	h = proc_header[sel->threads ? 2 : 0 | smpmode];
#else
	h = proc_header[2 | smpmode];
#endif
    }

    /* if we are showing usernames then we need to determine the longest one */
    if (sel->usernames)
    {
	/* calculate namelength from first "count" processes */
	kip = ((struct handle *)handle)->next_proc;
	n = ((struct handle *)handle)->remaining;
	if (n > count) n = count;
	namelength = 0;
	while (n-- > 0)
	{
	    w = strlen(username(PRUID(*kip)));
	    if (w > namelength) namelength = w;
	    kip++;
	}
	dprintf("format_process_header: namelength %d\n", namelength);

	/* place it in bounds */
	if (namelength < 8)
	{
	    namelength = 8;
	}

	/* these values are used just to format the header */
	n = -namelength;
	p = "USERNAME";
    }
    else
    {
	n = namelength = 6;
	p = "UID";
    }
    snprintf(p_header, MAX_COLS, "  PID %*s %s", n, p, h);

    return p_header;
}

static char fmt[MAX_COLS];		/* static area where result is built */
static char cmd[MAX_COLS];		/* static area for command column */

/* format to use when display_mode == 1 */
static char mode1_format[] = "%5d %-*.*s %6d %6d %6d %6d %6d %6d %6.2f%% %s";

char *
format_next_process(caddr_t handle, char *(*get_userid)(int))

{
    register struct kinfo_proc *pp;
    register long cputime;
    register double pct;
    register double wpct = 0.0;
    struct handle *hp;
    char status[16];
    char *userbuf;
    char *bufp;
    int state;

    /* find and remember the next proc structure */
    hp = (struct handle *)handle;
    pp = *(hp->next_proc++);
    hp->remaining--;
    
    /* get the process's command name in to "cmd" */
    if (show_fullcmd)
    {
	struct pargs pargs;
	int len;

	/* get the pargs structure */
	getkval((unsigned long)PP(pp, args), (int *)&pargs,
		sizeof(pargs), "!pargs");

	/* determine workable length */
	if ((len = pargs.ar_length) >= MAX_COLS)
	{
	    len = MAX_COLS - 1;
	}

	/* get the string from that */
	getkval((unsigned long)PP(pp, args) +
		sizeof(pargs.ar_ref) +
		sizeof(pargs.ar_length),
		(int *)cmd, len, "!cmdline");
    }
#if OSMAJOR <= 4
    else if ((PP(pp, flag) & P_INMEM) == 0)
#else
    else if ((PP(pp, sflag) & PS_INMEM) == 0)
#endif
    {
	/* Print swapped processes as <pname> */
	char *p;
	cmd[0] = '<';
	p = strcpyend(cmd+1, PP(pp, comm));
	*p++ = '>';
	*p = '\0';
    }
    else
    {
	/* take it straight out of p_comm */
	strncpy(cmd, PP(pp, comm), MAX_COLS-1);
    }

    /* convert the userid in to a string */
    userbuf = show_usernames ? username(PRUID(pp)) : itoa_w(PRUID(pp), namelength);

    /* handle the alternate display (i/o mode) */
    if (display_mode == 1)
    {
	/* format this entry */
	snprintf(fmt, MAX_COLS, mode1_format,
		 PP(pp, pid),
		 namelength, namelength,
		 userbuf,
		 per_second(SP(pp, vcsw), elapsed_msecs),
		 per_second(SP(pp, ivcsw), elapsed_msecs),
		 per_second(SP(pp, inblock), elapsed_msecs),
		 per_second(SP(pp, oublock), elapsed_msecs),
		 per_second(SP(pp, majflt), elapsed_msecs),
		 per_second(SP(pp, totalio), elapsed_msecs),
		 (SP(pp, totalio) * 100.) / total_io,
		 printable(cmd));
    }
    else /* normal display */
    {
	/*
	 * Convert the process's runtime from microseconds to seconds.  This
	 * time includes the interrupt time although that is not wanted here.
	 * ps(1) is similarly sloppy.
	 */
	cputime = (PP(pp, runtime) + 500000) / 1000000;

	/* calculate the base for cpu percentages */
	pct = pctdouble(PP(pp, pctcpu));

	/* generate "STATE" field */
	switch (state = PP(pp, stat)) {
	case SRUN:
	    if (smpmode && PP(pp, oncpu) != 0xff)
		sprintf(status, "CPU%d", PP(pp, oncpu));
	    else
		strcpy(status, "RUN");
	    break;
	case SSLEEP:
	    if (EP(pp, wmesg) != NULL) {
		sprintf(status, "%.6s", EP(pp, wmesg));
		break;
	    }
	    /* fall through */
	default:
	    if (state >= 0 &&
		state < sizeof(state_abbrev) / sizeof(*state_abbrev))
		sprintf(status, "%.6s", state_abbrev[(unsigned char) state]);
	    else
		sprintf(status, "?%-5d", state);
	    break;
	}

	/*
	 * Ready to format the entry.  There are two ways in which the display
	 * can vary, for a total of 4 possible different displays.  Instead of
	 * trying to handle all this with a single printf, we format the line
	 * piecemeal, building it up in the array "fmt".  The pointer bufp
	 * always points to the next part of fmt where characters need to go.
	 * Start by initializing bufp.
	 */
	bufp = fmt;

	/* format the pid and the username/uid */
	bufp += sprintf(bufp, "%5d %-*.*s ",
			PP(pp, pid),
			namelength, namelength, userbuf);

	/* show the number of threads if we are NOT showing
	   threads individually */
	if (!show_threads)
	{
	    bufp += sprintf(bufp, "%3d ", PP(pp, numthreads));
	}

	/* show priority, nice, size, rss, and state */
	bufp += sprintf(bufp, "%3d %3d%7s %6s %-6.6s",
#if OSMAJOR <= 4
			PP(pp, priority),
#else
			PP(pp, pri.pri_level),
#endif
			/* nice is shown exactly the same way that "ps" shows
			   it, with a NZERO bias and nothing else.  There
			   used to be code in here that did all sorts of
			   weird things depending on the priority class, but
			   the result was something unusual and inconsistent
			   with other tools.
			*/
			PP(pp, nice) - NZERO,
			format_k(PROCSIZE(pp)),
			format_k(pagetok(VP(pp, rssize))),
			status);

	/* if we have multiple processors, show the processor */
	if (smpmode)
	{
	    bufp += sprintf(bufp, " %1x", PP(pp, lastcpu));
	}

	/* show the cpu time */
	bufp += sprintf(bufp, "%7s ", format_time(cputime));

	/* if we are showing individual threads then we have room to
	   show weighted cpu percent */
	if (show_threads)
	{
	    wpct = weighted_cpu(pct, pp) * 100.0;  /* ??? */
	    bufp += sprintf(bufp, "%5.2f%% ", 100.0 * pct);
	}

	/* show cpu percent usage and the command */
	bufp += sprintf(bufp, "%5.2f%% %s",
			(double)PPCPU(pp) / 100.0,
			printable(cmd));
    }

    /* return the result */
    return(fmt);
}

/* comparison routines for qsort */

/*
 *  proc_compare - comparison function for "qsort"
 *	Compares the resource consumption of two processes using five
 *  	distinct keys.  The keys (in descending order of importance) are:
 *  	percent cpu, cpu ticks, state, resident set size, total virtual
 *  	memory usage.  The process states are ordered as follows (from least
 *  	to most important):  WAIT, zombie, sleep, stop, start, run.  The
 *  	array declaration below maps a process state index into a number
 *  	that reflects this ordering.
 */

static unsigned char sorted_state[] =
{
    0,	/* not used		*/
    3,	/* sleep		*/
    1,	/* ABANDONED (WAIT)	*/
    6,	/* run			*/
    5,	/* start		*/
    2,	/* zombie		*/
    4	/* stop			*/
};
 

#define ORDERKEY_PCTCPU \
  if (lresult = (long) PPCPU(p2) - (long) PPCPU(p1), \
     (result = lresult > 0 ? 1 : lresult < 0 ? -1 : 0) == 0)

#define ORDERKEY_CPTICKS \
  if ((result = PP(p2, runtime) > PP(p1, runtime) ? 1 : \
                PP(p2, runtime) < PP(p1, runtime) ? -1 : 0) == 0)

#define ORDERKEY_STATE \
  if ((result = sorted_state[(unsigned char) PP(p2, stat)] - \
                sorted_state[(unsigned char) PP(p1, stat)]) == 0)

#if OSMAJOR <= 4
#define ORDERKEY_PRIO \
  if ((result = PP(p2, priority) - PP(p1, priority)) == 0)
#else
#define ORDERKEY_PRIO \
  if ((result = PP(p2, pri.pri_level) - PP(p1, pri.pri_level)) == 0)
#endif

#define ORDERKEY_RSSIZE \
  if ((result = VP(p2, rssize) - VP(p1, rssize)) == 0) 

#define ORDERKEY_MEM \
  if ( (result = PROCSIZE(p2) - PROCSIZE(p1)) == 0 )

#define ORDERKEY_IO \
  if ( (result = SP(p2, totalio) - SP(p1, totalio)) == 0)

/* compare_cpu - the comparison function for sorting by cpu percentage */

int
proc_compare(struct proc **pp1, struct proc **pp2)

{
    register struct kinfo_proc *p1;
    register struct kinfo_proc *p2;
    register int result;
    register pctcpu lresult;

    /* remove one level of indirection */
    p1 = *(struct kinfo_proc **) pp1;
    p2 = *(struct kinfo_proc **) pp2;

    ORDERKEY_PCTCPU
    ORDERKEY_CPTICKS
    ORDERKEY_STATE
    ORDERKEY_PRIO
    ORDERKEY_RSSIZE
    ORDERKEY_MEM
    ;

    return(result);
}

/* compare_size - the comparison function for sorting by total memory usage */

int
compare_size(struct proc **pp1, struct proc **pp2)

{
    register struct kinfo_proc *p1;
    register struct kinfo_proc *p2;
    register int result;
    register pctcpu lresult;

    /* remove one level of indirection */
    p1 = *(struct kinfo_proc **) pp1;
    p2 = *(struct kinfo_proc **) pp2;

    ORDERKEY_MEM
    ORDERKEY_RSSIZE
    ORDERKEY_PCTCPU
    ORDERKEY_CPTICKS
    ORDERKEY_STATE
    ORDERKEY_PRIO
    ;

    return(result);
}

/* compare_res - the comparison function for sorting by resident set size */

int
compare_res(struct proc **pp1, struct proc **pp2)

{
    register struct kinfo_proc *p1;
    register struct kinfo_proc *p2;
    register int result;
    register pctcpu lresult;

    /* remove one level of indirection */
    p1 = *(struct kinfo_proc **) pp1;
    p2 = *(struct kinfo_proc **) pp2;

    ORDERKEY_RSSIZE
    ORDERKEY_MEM
    ORDERKEY_PCTCPU
    ORDERKEY_CPTICKS
    ORDERKEY_STATE
    ORDERKEY_PRIO
    ;

    return(result);
}

/* compare_time - the comparison function for sorting by total cpu time */

int
compare_time(struct proc **pp1, struct proc **pp2)

{
    register struct kinfo_proc *p1;
    register struct kinfo_proc *p2;
    register int result;
    register pctcpu lresult;
  
    /* remove one level of indirection */
    p1 = *(struct kinfo_proc **) pp1;
    p2 = *(struct kinfo_proc **) pp2;

    ORDERKEY_CPTICKS
    ORDERKEY_PCTCPU
    ORDERKEY_STATE
    ORDERKEY_PRIO
    ORDERKEY_RSSIZE
    ORDERKEY_MEM
    ;

      return(result);
  }
  
/* compare_prio - the comparison function for sorting by priority */

int
compare_prio(struct proc **pp1, struct proc **pp2)

{
    register struct kinfo_proc *p1;
    register struct kinfo_proc *p2;
    register int result;
    register pctcpu lresult;

    /* remove one level of indirection */
    p1 = *(struct kinfo_proc **) pp1;
    p2 = *(struct kinfo_proc **) pp2;

    ORDERKEY_PRIO
    ORDERKEY_CPTICKS
    ORDERKEY_PCTCPU
    ORDERKEY_STATE
    ORDERKEY_RSSIZE
    ORDERKEY_MEM
    ;

    return(result);
}

/* compare_prio - the comparison function for sorting by io count */

int
compare_io(struct proc **pp1, struct proc **pp2)

{
    register struct kinfo_proc *p1;
    register struct kinfo_proc *p2;
    register int result;
    register pctcpu lresult;

    /* remove one level of indirection */
    p1 = *(struct kinfo_proc **) pp1;
    p2 = *(struct kinfo_proc **) pp2;

    ORDERKEY_IO
    ORDERKEY_PCTCPU
    ORDERKEY_CPTICKS
    ORDERKEY_STATE
    ORDERKEY_PRIO
    ORDERKEY_RSSIZE
    ORDERKEY_MEM
    ;

    return(result);
}

/*
 * proc_owner(pid) - returns the uid that owns process "pid", or -1 if
 *		the process does not exist.
 *		It is EXTREMLY IMPORTANT that this function work correctly.
 *		If top runs setuid root (as in SVR4), then this function
 *		is the only thing that stands in the way of a serious
 *		security problem.  It validates requests for the "kill"
 *		and "renice" commands.
 */

int
proc_owner(int pid)

{
    register int cnt;
    register struct kinfo_proc **prefp;
    register struct kinfo_proc *pp;

    prefp = pref;
    cnt = pref_len;
    while (--cnt >= 0)
    {
	pp = *prefp++;	
	if (PP(pp, pid) == (pid_t)pid)
	{
	    return((int)PRUID(pp));
	}
    }
    return(-1);
}


/*
 * swapmode is based on a program called swapinfo written
 * by Kevin Lahey <kml@rokkaku.atl.ga.us>.
 */

#define	SVAR(var) __STRING(var)	/* to force expansion */
#define	KGET(idx, var)							\
	KGET1(idx, &var, sizeof(var), SVAR(var))
#define	KGET1(idx, p, s, msg)						\
	KGET2(nlst[idx].n_value, p, s, msg)
#define	KGET2(addr, p, s, msg)						\
	if (kvm_read(kd, (u_long)(addr), p, s) != s) {		        \
		warnx("cannot read %s: %s", msg, kvm_geterr(kd));       \
		return (0);                                             \
       }
#define	KGETRET(addr, p, s, msg)					\
	if (kvm_read(kd, (u_long)(addr), p, s) != s) {			\
		warnx("cannot read %s: %s", msg, kvm_geterr(kd));	\
		return (0);						\
	}


int
swapmode(int *retavail, int *retfree)

{
	int n;
	int pagesize = getpagesize();
	struct kvm_swap swapary[1];

	*retavail = 0;
	*retfree = 0;

#define CONVERT(v)	((quad_t)(v) * pagesize / 1024)

	n = kvm_getswapinfo(kd, swapary, 1, 0);
	if (n < 0 || swapary[0].ksw_total == 0)
		return(0);

	*retavail = CONVERT(swapary[0].ksw_total);
	*retfree = CONVERT(swapary[0].ksw_total - swapary[0].ksw_used);

	n = (int)((double)swapary[0].ksw_used * 100.0 /
	    (double)swapary[0].ksw_total);
	return(n);
}

