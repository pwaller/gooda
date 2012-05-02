/*
Copyright 2012 Google Inc. All Rights Reserved.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

 */
#include <sys/types.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <stddef.h>
#include <unistd.h>
#include <errno.h>
#include <string.h>
#include <getopt.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <err.h>
#include "perf_event.h"
#include "gooda.h"
#include "perf_gooda.h"
#include "gooda_util.h"

int max_record=0, record_count=0;

int num_comm=0,num_fork=0,num_sample=0,num_mmap=0,num_lost=0,num_exit=0,num_throttle=0,num_unthrottle=0,num_read=0;
uint64_t tsc_now=0, this_time=0;
int lbr_flag = 0, lbr_any = 0, lbr_ret = 0, lbr_call = 0, lbr_ind = 0;

mmap_struc_ptr  mmap_stack = NULL, mmap_current = NULL, kernel_mmap, previous_mmap;
comm_struc_ptr  comm_stack = NULL, comm_current = NULL;
process_struc_ptr process_stack=NULL, active_proc_stack=NULL, current_process=NULL;
process_struc_ptr principal_process_stack=NULL;
function_struc_ptr global_func_stack=NULL;
pointer_data *process_list;
derived_sample_data* derived_events = NULL;

int num_process=0, global_func_count=0, global_sample_count_in_func=0,global_branch_sample_count=0;
int bad_rva =0, global_rva = 0,bad_sample_count=0,total_function_sample_count = 0;
int asm_cutoff = 20, func_cutoff = 50, source_cutoff = 50, max_bb = 500, max_branch = 10;
int num_branch, num_sub_branch, num_derived;
int source_index=0, target_index=0, source_column = 0, target_column = 0;
int *id_array, num_cores, num_sockets=2, *socket, num_events;
uint64_t min_event_id=0xFFFFFFFFFFFFFFFFUL;
int default_hash_length=10000, max_default_entries=2000;
double sqrt_five, max_entry_fraction = 0.2, sum_cutoff = 0.95;
int pop_threshold=0xFF;
int *global_sample_count, total_sample_count=0;
double *global_multiplex_correction, uop_issue_rate = 3.0;
event_order_struc_ptr global_event_order;
char **fixed_name_list, **branch_name_list;
int * fixed_event_index;
int column_flag, debug_flag=0;
char return_event[]="br_inst_retired:near_return";

int global_flag1 = 0, global_flag2 = 0;
event_attr_ptr global_attrs;
event_id_ptr global_event_ids;
event_name_struc_ptr event_list;
int family, model;
char *arch, *cpu_desc;
int min_id_event=-1, max_id_event=-1;

int num_lbr;
typedef struct lbr_record_struc{
	uint64_t	source;
	uint64_t	destination;
	int		mispredict;
	}lbr_record_data;
lbr_record_data* lbr_data;

	
mmap_struc_ptr mmap_ll=NULL;
lost_struc_ptr lost_ll=NULL;
comm_struc_ptr comm_ll=NULL;
exit_struc_ptr exit_ll=NULL;
throttle_struc_ptr throttle_ll=NULL;
unthrottle_struc_ptr untrottle_ll=NULL;
fork_struc_ptr fork_ll=NULL;
read_struc_ptr read_ll=NULL;
sample_struc_ptr sampl_ll=NULL;
buildid_struc_ptr build_ll=NULL;

void* reorder_process();

typedef void (*record_ops_t)(bufdesc_t *desc, struct perf_event_header *ehdr);

static const char *__perf_magic = "PERFFILE";
static const uint64_t __perf_magic2    = 0x32454c4946524550ULL;
static const uint64_t __perf_magic2_sw = 0x50455246494c4532ULL;

static event_id_t *event_ids;		/* table of all the event ids */
static struct perf_file_attr *attrs;	/* table of all attrs */
static int nr_attrs;			/* number of elements in attrs */
static int nr_ids;			/* number of elements in event_ids */

static int read_attr_from_file(bufdesc_t *desc, struct perf_file_attr *attrs);

static void (*read_feature[HEADER_LAST_FEATURE])(bufdesc_t *, struct perf_file_header *);

/*
 * read a chunk of buffer. Use actual file read for now.
 * Could use mmap() in the future
 */
static void
raw_read_buffer(bufdesc_t *desc, void *addr, size_t sz)
{
        ssize_t ret;
        off_t off;

        if ((desc->cur.pos + sz) > desc->cur.end)
                err(1, "trying to read beyond the end of the section");

        off = lseek(desc->fd, desc->cur.pos, SEEK_SET);
        if (off == (off_t)-1)
                err(1, "cannot seek to position %"PRIu64, desc->cur.pos);

        ret = read(desc->fd, addr, sz);
        if (ret < sz)
                err(1, "cannot read %zu bytes", sz);

        desc->cur.pos += sz;
}

/*
 * skip over a sz-sized chunk of the buffer
 */
static int
raw_skip_buffer(bufdesc_t *desc, size_t sz)
{
	if ((desc->cur.pos + sz) > desc->cur.end)
		return -1;

	lseek(desc->fd, sz, SEEK_CUR);
	desc->cur.pos += sz;
	return 0;
}

/*
 * read data section from the buffer. Will stop
 * when the end of the data section is reached
 *
 * In effect this function reads from offset 0
 * till end of data section (where samples are
 * saved).
 */
static int
read_buffer(bufdesc_t *desc, void *addr, size_t sz)
{
	if (desc->cur.pos + sz > desc->data.end)
		return -1;

	raw_read_buffer(desc, addr, sz);
	return 0;
}

/*
 * skip sz-sized chunk, but no beyond the end of
 * the data section
 */
static int
skip_buffer(bufdesc_t *desc, size_t sz)
{
	if (desc->cur.pos + sz >= desc->data.end)
		return -1;
	return raw_skip_buffer(desc, sz);
}

/*
 * appended to sample: comm, fork, mmap, throttle, unthrottle, exit, lost
 * when sample_id_all is set
 *
 * contains mostly identifications to associate event to process, time, cpu.
 * actual content depends on sample_type
 */
static void
display_id(bufdesc_t *desc, struct perf_event_header *ehdr)
{
	struct { uint32_t pid, tid; } pid;
	uint64_t type = desc->sample_type;
	uint64_t val64, id = -1;
	int ret;

	if (type & PERF_SAMPLE_TID) {
		ret = read_buffer(desc, &pid, sizeof(pid));
		if (ret)
			errx(1, "cannot read PID");
#ifdef DBUG
		fprintf(stderr," PID:%d TID:%d", pid.pid, pid.tid);
#endif
	}

	if (type & PERF_SAMPLE_TIME) {
		ret = read_buffer(desc, &val64, sizeof(val64));
		if (ret)
			errx(1, "cannot read time");

#ifdef DBUG
		fprintf(stderr," TIME:%'"PRIu64, val64);
#endif
	}

	if (type & PERF_SAMPLE_ID) {
		ret = read_buffer(desc, &id, sizeof(id));
		if (ret)
			errx(1, "cannot read id");

#ifdef DBUG
		fprintf(stderr," ID:%"PRIu64, id);
#endif
	}

	if (type & PERF_SAMPLE_STREAM_ID) {
		ret = read_buffer(desc, &val64, sizeof(val64));
		if (ret)
			errx(1, "cannot read stream_id");

#ifdef DBUG
		fprintf(stderr," STREAM_ID:%"PRIu64, val64);
#endif
	}

	if (type & PERF_SAMPLE_CPU) {
		struct { uint32_t cpu, reserved; } cpu;
		ret = read_buffer(desc, &cpu, sizeof(cpu));
		if (ret)
			errx(1, "cannot read cpu");
#ifdef DBUG
		fprintf(stderr," CPU:%u", cpu.cpu);
#endif
	}
#ifdef DBUG
	fputc('\n',stderr);
#endif
}

static void
display_lost(bufdesc_t *desc, struct perf_event_header *ehdr)
{
	struct { uint64_t id, lost; } lost;
	int ret;

	ret = read_buffer(desc, &lost, sizeof(lost));
	if (ret)
		errx(1, "cannot read lost info");

	/* lost samples for event */
#ifdef DBUG
	fprintf(stderr,"LOST: SAMPLES:%"PRIu64" EVENT:%"PRIu64, lost.lost, lost.id);
#endif
	if (desc->sample_id_all)
		display_id(desc, ehdr);
#ifdef DBUG
	else
		fputc('\n',stderr);
#endif
}

static void
display_exit(bufdesc_t *desc, struct perf_event_header *ehdr)
{
	struct {
		uint32_t pid, ppid;
		uint32_t tid, ptid;
		uint64_t time;
	} grp;
	int ret;

	ret = read_buffer(desc, &grp, sizeof(grp));
	if (ret)
		errx(1, "cannot read exit info");

#ifdef DBUG
	fprintf(stderr,"EXIT: PID:%d TID:%d TIME:%"PRIu64, grp.pid, grp.tid, grp.time);
#endif
	if (desc->sample_id_all)
		display_id(desc, ehdr);
#ifdef DBUG
	else
		fputc('\n',stderr);
#endif
}

static void
display_throttle(bufdesc_t *desc, struct perf_event_header *ehdr)
{
	struct { uint64_t time, id, stream_id; } thr;
	int i, ret;

	ret = read_buffer(desc, &thr, sizeof(thr));
	if (ret)
		errx(1, "cannot read throttling info");

	/*
 	 * correlate event id to actual attr so we can print the config field
 	 * to identify (somewhat) the event
 	 */
	for (i = 0 ; i < nr_ids; i++)
		if (event_ids[i].id == thr.id)
			break;

#ifdef DBUG
	if (i == nr_ids)
		fprintf(stderr,"THROTTLE: EVENT:%"PRIu64" CFG:??? STREAMID:%"PRIu64, thr.id, thr.stream_id);
	else
		fprintf(stderr,"THROTTLE: EVENT:%"PRIu64" CFG:0x%"PRIx64" STREAMID:%"PRIu64,
			thr.id,
			attrs[event_ids[i].attr_id].attr.config,
			thr.stream_id);
#endif

	if (desc->sample_id_all)
		display_id(desc, ehdr);
#ifdef DBUG
	else
		fputc('\n',stderr);
#endif
}

static void
display_unthrottle(bufdesc_t *desc, struct perf_event_header *ehdr)
{
	struct { uint64_t time, id, stream_id; } thr;
	int i, ret;

	ret = read_buffer(desc, &thr, sizeof(thr));
	if (ret)
		errx(1, "cannot read throttling info");

	/*
 	 * correlate event id to actual attr so we can print the config field
 	 * to identify (somewhat) the event
 	 */
	for (i = 0 ; i < nr_ids; i++)
		if (event_ids[i].id == thr.id)
			break;

#ifdef DBUG
	if (i == nr_ids)
		fprintf(stderr,"UNTHROTTLE: EVENT:%"PRIu64" CFG:??? STREAMID:%"PRIu64, thr.id, thr.stream_id);
	else
		fprintf(stderr,"UNTHROTTLE: EVENT:%"PRIu64" CFG:0x%"PRIx64" STREAMID:%"PRIu64,
			thr.id,
			attrs[event_ids[i].attr_id].attr.config,
			thr.stream_id);
#endif

	if (desc->sample_id_all)
		display_id(desc, ehdr);
#ifdef DBUG
	else
		fputc('\n',stderr);
#endif
}

static size_t
sample_all_id_size(bufdesc_t *desc)
{
	struct { uint32_t pid, tid; } pid;
	size_t sz = 0;
	int type = desc->sample_type;

	if (!desc->sample_id_all)
		return 0;

	if (type & PERF_SAMPLE_TID)
		sz += sizeof(pid);

	if (type & PERF_SAMPLE_TIME)
		sz += sizeof(uint64_t);

	if (type & PERF_SAMPLE_ID)
		sz += sizeof(uint64_t);

	if (type & PERF_SAMPLE_STREAM_ID)
		sz += sizeof(uint64_t);

	if (type & PERF_SAMPLE_CPU) {
		struct { uint32_t cpu, reserved; } cpu;
		sz += sizeof(cpu);
	}
	return sz;
}

static void
display_comm(bufdesc_t *desc, struct perf_event_header *ehdr)
{
	struct {
		uint32_t pid, tid;
		char comm[0];
	} comm;
	char *str = NULL;
	size_t sz, sample_all_sz;
	int ret;
        comm_struc_ptr local_comm;
        process_struc_ptr this_process;

	ret = read_buffer(desc, &comm, sizeof(comm));
	if (ret)
		errx(1, "cannot read comm data");

	sample_all_sz = sample_all_id_size(desc);

	sz = ehdr->size - sizeof(comm) - sizeof(*ehdr) - sample_all_sz;
	str = malloc(sz);
	if (!str)
		err(1, "cannot allocate memory for comm len=%zu", sz);

	ret = read_buffer(desc, str, sz);
	if (ret)
		err(1, "cannot read comm name");

#ifdef DBUG
	fprintf(stderr,"COMM: PID:%d TID:%d COMM:%s",
		comm.pid,
		comm.tid,
		str);
#endif

#ifdef ANALYZE
        local_comm = comm_struc_create();
        if(local_comm == NULL)
                {
                fprintf(stderr," failed to create comm struc in display_comm\n");
                err(1, "failed to create comm in display comm");
                }

        local_comm->pid = comm.pid;
        local_comm->tid = comm.tid;
        local_comm->name = str;
        local_comm->time = this_time;

        this_process = insert_comm(local_comm);
#endif

#ifndef ANALYZE
	free(str);
#endif

	if (desc->sample_id_all)
		display_id(desc, ehdr);
#ifdef DBUG
	else
		fputc('\n',stderr);
#endif
}

static void
display_fork(bufdesc_t *desc, struct perf_event_header *ehdr)
{
	struct {
		uint32_t pid, ppid;
		uint32_t tid, ptid;
		uint64_t time; // optional, only if PERF_SAMPLE_TIME
	} f;
	size_t sz = sizeof(f);
	int ret;
	fork_struc_ptr f_str;

	if (!desc->sample_id_all) {
		/*
		 * try to guess if PERF_SAMPLE_TIME was used
		 * if sz < sizeof(f), then no time field
		 */
		sz = ehdr->size - sizeof(*ehdr);
		if (sz > sizeof(f))
			errx(1, "wrong sample size for fork");
	} else
		sz -= sizeof(uint64_t);

	ret = read_buffer(desc, &f, sz);
	if (ret)
		errx(1, "cannot read fork data");

#ifdef DBUG
	fprintf(stderr,"FORK: PID:%d TID:%d PPID:%d PTID:%d",
		f.pid,
		f.tid,
		f.ppid,
		f.ptid);
#endif

	if (desc->sample_id_all)
		display_id(desc, ehdr);
#ifdef DBUG
	else if (sz == sizeof(f))
		fprintf(stderr," TIME:%"PRIu64"\n", f.time);
	else
		fputc('\n',stderr);
#endif

#ifdef ANALYZE
        f_str = fork_struc_create();
        if(f_str == NULL)
                {
                fprintf(stderr," failed to create fork struc in display fork\n");
                err(1, "failed to create fork struc in display fork");
                }
	f_str->pid = f.pid;
	f_str->ppid = f.ppid;
	f_str->tid = f.tid;
	f_str->ptid = f.ptid;
	if (sz == sizeof(f)) f_str->time = f.time;

        insert_fork(f_str);
#endif


}

static void
display_read(bufdesc_t *desc, struct perf_event_header *ehdr)
{
	skip_buffer(desc, ehdr->size - sizeof(*ehdr));
}

static void
perf_display_raw(bufdesc_t *desc)
{
	size_t sz = 0;
	uint32_t raw_sz, i;
	char *buf;
	int ret;

	ret = read_buffer(desc, &raw_sz, sizeof(raw_sz));
	if (ret)
		errx(1, "cannot read raw size");

	sz += sizeof(raw_sz);

#ifdef DBUG
	fprintf(stderr,"\n\tRAWSZ:%u\n", raw_sz);
#endif

	buf = malloc(raw_sz);
	if (!buf)
		err(1, "cannot allocate raw buffer");

	ret = read_buffer(desc, buf, raw_sz);
	if (ret) {
		free(buf);
		errx(1, "cannot read raw data");
	}

#ifdef DBUG
	if (raw_sz)
		fputc('\t',stderr);

	for(i=0; i < raw_sz; i++) {
		fprintf(stderr,"0x%02x ", buf[i] & 0xff );
		if (((i+1) % 16)  == 0)
			fprintf(stderr,"\n\t");
	}
	if (raw_sz)
		fputc('\n',stderr);
#endif

	free(buf);
}

static void
perf_display_branch_stack(bufdesc_t *desc)
{
       struct perf_branch_entry b;
       uint64_t nr;
       int ret, i;

       ret = read_buffer(desc, &nr, sizeof(nr));
       if (ret)
               errx(1, "cannot read branch stack nr");
#ifdef ANALYZE
	lbr_data = (lbr_record_data *)calloc(1,sizeof(lbr_record_data)*nr);
	if(lbr_data == NULL)
		err(1,"failed to allocate LBR record buffer in perf_display_branch_stack");
	num_lbr = nr;
	i = 0;
#endif
#ifdef DBUG
       fprintf(stderr,"\n\tBRANCH_STACK:%"PRIu64"\n", nr);
#endif

       while (nr--) {
               ret = read_buffer(desc, &b, sizeof(b));
               if (ret)
                       errx(1, "cannot read branch stack entry");
#ifdef ANALYZE
		lbr_data[i].source = b.from;
		lbr_data[i].destination = b.to;
		lbr_data[i].mispredict = b.mispredicted;
		i++;
#endif
#ifdef DBUG
               fprintf(stderr,"\tFROM:0x%016"PRIx64" TO:0x%016"PRIx64" MISPRED:%c\n",
                       b.from,
                       b.to,
                       !(b.mispredicted || b.predicted) ? '-':
                       (b.mispredicted ? 'Y' :'N'));
#endif
       }
}

static void
display_sample(bufdesc_t *desc, struct perf_event_header *ehdr)
{
	struct { uint32_t pid, tid; } pid;
	uint64_t type = desc->sample_type;
	uint64_t val64, ip, event_id = -1, id = -1, orig_event_id;
	uint64_t time_enabled, time_running;
	struct { uint32_t cpu, reserved; } cpu;
	int ret, i,j,k;
        mmap_struc_ptr local_mmap, target_mmap;
	process_struc_ptr principal_process;
	module_struc_ptr this_module;

	/*
	 * the sample_type information is laid down
	 * based on the PERF_RECORD_SAMPLE format specified
	 * in the perf_event.h header file.
	 *
	 * That order is different from the enum perf_event_sample_format
	 * The order of the if (type & ...) is thus important. Do not alter
	 */

        local_mmap = NULL;
        num_sample++;
        total_sample_count++;
        event_id = -1;

#ifdef DBUG
	fprintf(stderr,"SAMPLE: ");
#endif

	if (type & PERF_SAMPLE_IP) {
		const char *xtra = " ";
		ret = read_buffer(desc, &val64, sizeof(val64));
		if (ret)
			errx(1, "cannot read IP");
		/*
		 * MISC_EXACT_IP indicates that kernel is returning
		 * th  IIP of an instruction which caused the event, i.e.,
		 * no skid. PEBS + LBR used on Intel x86.
		 */
		if (ehdr->misc & PERF_RECORD_MISC_EXACT_IP)
			xtra = " (exact) ";

#ifdef DBUG
		fprintf(stderr,"IIP:%#016"PRIx64"%s", val64, xtra);
#endif

                ip = val64;
	}

	if (type & PERF_SAMPLE_TID) {
		ret = read_buffer(desc, &pid, sizeof(pid));
		if (ret)
			errx(1, "cannot read PID");

#ifdef DBUG
		fprintf(stderr,"PID:%d TID:%d ", pid.pid, pid.tid);
#endif
	}

	if (type & PERF_SAMPLE_TIME) {
		ret = read_buffer(desc, &val64, sizeof(val64));
		if (ret)
			errx(1, "cannot read time");

#ifdef DBUG
		fprintf(stderr,"TIME:%'"PRIu64" ", val64);
#endif

                this_time = val64;

	}

	if (type & PERF_SAMPLE_ADDR) {
		ret = read_buffer(desc, &val64, sizeof(val64));
		if (ret)
			errx(1, "cannot read addr");

#ifdef DBUG
		fprintf(stderr,"ADDR:%#016"PRIx64" ", val64);
#endif
	}

	if (type & PERF_SAMPLE_ID) {
		ret = read_buffer(desc, &id, sizeof(id));
		if (ret)
			errx(1, "cannot read id");

#ifdef DBUG
		fprintf(stderr,"ID:%"PRIu64" ", id);
#endif

                event_id = id;

	}

	if (type & PERF_SAMPLE_STREAM_ID) {
		ret = read_buffer(desc, &val64, sizeof(val64));
		if (ret)
			errx(1, "cannot read stream_id");

#ifdef DBUG
		fprintf(stderr,"STREAM_ID:%"PRIu64" ", val64);
#endif
	}

	if (type & PERF_SAMPLE_CPU) {
		ret = read_buffer(desc, &cpu, sizeof(cpu));
		if (ret)
			errx(1, "cannot read cpu");
#ifdef DBUG
		fprintf(stderr,"CPU:%u ", cpu.cpu);
#endif
	}

	if (type & PERF_SAMPLE_PERIOD) {
		ret = read_buffer(desc, &val64, sizeof(val64));
		if (ret)
			errx(1, "cannot read period");
#ifdef DBUG
		fprintf(stderr,"PERIOD:%'"PRIu64" ", val64);
#endif
	}

	/* struct read_format {
	 * 	{ u64		value;
	 * 	  { u64		time_enabled; } && PERF_FORMAT_ENABLED
	 * 	  { u64		time_running; } && PERF_FORMAT_RUNNING
	 * 	  { u64		id;           } && PERF_FORMAT_ID
	 * 	} && !PERF_FORMAT_GROUP
	 *
	 * 	{ u64		nr;
	 * 	  { u64		time_enabled; } && PERF_FORMAT_ENABLED
	 * 	  { u64		time_running; } && PERF_FORMAT_RUNNING
	 * 	  { u64		value;
	 * 	    { u64	id;           } && PERF_FORMAT_ID
	 * 	  }		cntr[nr];
	 * 	} && PERF_FORMAT_GROUP
	 * };
	 */
	if (type & PERF_SAMPLE_READ) {
		uint64_t nr, fmt;
		int i;

		if (id == -1)
			errx(1, "cannot resolve PERF_SAMPLE_ID, event does not have PERF_SAMPLE_ID set");

		for (i = 0; i < nr_ids; i++)
			if (id == event_ids[i].id)
				break;
		if (i == nr_ids)
			errx(1, "cannot find id %"PRIu64" to parse PERF_SAMPLE_READ", id);

		fmt = attrs[event_ids[i].attr_id].attr.read_format;

		if (fmt & PERF_FORMAT_GROUP) {
			ret = read_buffer(desc, &nr, sizeof(nr));
			if (ret)
				errx(1, "cannot read nr");

			time_enabled = time_running = 1;

			if (fmt & PERF_FORMAT_TOTAL_TIME_ENABLED) {
				ret = read_buffer(desc, &time_enabled, sizeof(time_enabled));
				if (ret)
					errx(1, "cannot read timing info");
			}

			if (fmt & PERF_FORMAT_TOTAL_TIME_RUNNING) {
				ret = read_buffer(desc, &time_running, sizeof(time_running));
				if (ret)
					errx(1, "cannot read timing info");
			}

#ifdef DBUG
//			fprintf(stderr,"ENA=%'"PRIu64" RUN=%'"PRIu64" NR=%"PRIu64" ", time_enabled, time_running, nr);
			fprintf(stderr,"ENA=%"PRIu64" RUN=%"PRIu64" NR=%"PRIu64" \n", time_enabled, time_running, nr);
#endif

			while(nr--) {
				ret = read_buffer(desc, &val64, sizeof(val64));
				if (ret) 
					errx(1, "cannot read group value");

				if (fmt & PERF_FORMAT_ID) {
					ret = read_buffer(desc, &id, sizeof(id));
					if (ret)
						errx(1, "cannot read leader id");
#ifdef DBUG
					fprintf(stderr,"ID:%"PRIu64" ", id);
#endif
				}
#ifdef DBUG
				fprintf(stderr,"VAL:%"PRIu64" \n", val64);
#endif
			}
		} else {
			/*
			 * this program does not use FORMAT_GROUP when there is only one event
			 */
			ret = read_buffer(desc, &val64, sizeof(val64));
			if (ret)
				errx(1, "cannot read value");

			if (fmt & PERF_FORMAT_TOTAL_TIME_ENABLED) {
				ret = read_buffer(desc, &time_enabled, sizeof(time_enabled));
				if (ret)
					errx(1, "cannot read timing info");
			}

			if (fmt & PERF_FORMAT_TOTAL_TIME_RUNNING) {
				ret = read_buffer(desc, &time_running, sizeof(time_running));
				if (ret)
					errx(1, "cannot read timing info");
			}
#ifdef DBUG
			fprintf(stderr,"ENA:%"PRIu64" RUN:%"PRIu64" \n", time_enabled, time_running);
#endif

			if (fmt & PERF_FORMAT_ID) {
				ret = read_buffer(desc, &id, sizeof(id));
				if (ret)
					errx(1, "cannot read leader id");
#ifdef DBUG
				fprintf(stderr,"ID:%"PRIu64" \n", id);
#endif
			}

#ifdef DBUG
			fprintf(stderr,"VAL:%"PRIu64" \n", val64);
#endif
		}
	}

	if (type & PERF_SAMPLE_CALLCHAIN) {
		uint64_t nr, ip;

		ret = read_buffer(desc, &nr, sizeof(nr));
		if (ret)
			errx(1, "cannot read callchain nr");

		while(nr--) {
			ret = read_buffer(desc, &ip, sizeof(ip));
			if (ret)
				errx(1, "cannot read ip");

#ifdef DBUG
			fprintf(stderr,"\t0x%"PRIx64"\n", ip);
#endif
		}
	}

	if (type & PERF_SAMPLE_RAW)
		perf_display_raw(desc);

	if (type & PERF_SAMPLE_BRANCH_STACK)
		perf_display_branch_stack(desc);

#ifdef DBUG
	fputc('\n',stderr);
#endif

#ifdef ANALYZE
#ifdef DBUGA
        fprintf(stderr," about to call bind_sample for sample at ip = 0x%"PRIx64", pid = %u\n",ip,pid.pid);
#endif
        local_mmap = bind_sample(pid.pid,ip,this_time);
        if(local_mmap == NULL)
                {
#ifdef DBUGA
                fprintf(stderr," could not find mmap for sample with pid = %u, ip = 0x%"PRIx64", at time = 0x%"PRIx64"\n",pid.pid,ip,this_time);
        //      err(1,"failed to find mmap for sample");
#endif
                return;
                }
	current_process = find_process_struc(pid.pid);
	debug_flag = 0;
//	debug printout to explore process merging
/*
	fprintf(stderr,"display_event, current_process name = %s, address = %p, pid = %u\n",current_process->name, current_process,pid.pid);
	fprintf(stderr,"display_event, mmap path = %s, principal process address = %p, princ_proc_stack addr = %p\n",
			local_mmap->filename, local_mmap->principal_process,principal_process_stack);
	if(current_process != NULL)
		{
		if((current_process->name[0] == 'r') && (current_process->name[1] == 'e') && (current_process->name[2] == 'a'))
			{
			debug_flag = 1;
			fprintf(stderr,"setting debug_flag to 1, current_process name = %s, address = %p\n",current_process->name, current_process);
			}
		}
//	debug_flag = 1;
*/
	principal_process = local_mmap->principal_process;
	if(local_mmap->principal_process == NULL)
		{
		principal_process = find_principal_process(local_mmap);
//		if(debug_flag == 1)
//		fprintf(stderr,"returned from find_principal_process with address %p\n",principal_process);
//		if(principal_process != NULL)
//			fprintf(stderr,"returned from find_principal_process with name %s, address %p\n",principal_process->name,principal_process);
//		if(debug_flag == 1)
//		fprintf(stderr,"local_mmap->principal_process = %p\n",local_mmap->principal_process);
		}
//	else
//		{
//		if(debug_flag == 1)
//		fprintf(stderr,"did not call find_principal_process with address %p\n",principal_process);
//		if(principal_process != NULL)
//			fprintf(stderr,"did not call find_principal_process with name %s, address %p\n",principal_process->name,principal_process);
//		if(debug_flag == 1)
//		fprintf(stderr,"local_mmap->principal_process = %p\n",local_mmap->principal_process);
//		}
	this_module = local_mmap->this_module;
	if(local_mmap->this_module == NULL)
		{
//		if(debug_flag == 1)
//		fprintf(stderr,"calling bind_mmap local_mmap->this_module = NULL\n");
		this_module = bind_mmap(local_mmap);
//		if(debug_flag == 1)
//		fprintf(stderr,"found module with bind_mmap, this_module path = %s, address %p\n",this_module->path,this_module);
		}
//	else
//		{
//		if(debug_flag == 1)
//		fprintf(stderr,"found module in mmap, this_module address %p\n",this_module);
//		if(debug_flag == 1)
//		fprintf(stderr,"found module in mmap, this_module path = %s, address %p\n",this_module->path,this_module);
//		}
	orig_event_id = event_id;
	if(event_id < min_event_id)fprintf(stderr,"BAD EVENT ID = %ld, min_event_id = %ld\n",event_id,min_event_id);
        if(event_id == -1)
                {
                event_id = 0;
                }
        else
                {
                event_id =  id_array[(int) (event_id - min_event_id)];
                }
	if(event_id > num_events)fprintf(stderr,"BAD EVENT ID orig = %ld, event_id = %ld\n",orig_event_id,event_id);
#ifdef DBUGA
        fprintf(stderr," found mmap for sample with pid = %d, ip = 0x%"PRIx64", at time = 0x%"PRIx64"\n",pid.pid,ip,this_time);
        fprintf(stderr," entering increment module structure, pid = %u, tid = %u, ip = 0x%"PRIx64",cpu = %d, mmap base = 0x%"PRIx64",time_enabled = %ld, time_running = %ld, id = %lu, event_id = %lu, orig_event_id = %lu\n",
		pid.pid,pid.tid,ip,cpu.cpu, local_mmap->addr,time_enabled,time_running,id,event_id,orig_event_id);
#endif

        ret = increment_module_struc(pid.pid,pid.tid,ip,event_id,cpu.cpu,local_mmap,time_enabled, time_running);

		if(debug_flag == 1)
#ifdef DBUGA
        fprintf(stderr," returned from increment module\n");
#endif
        if(ret != 0)
                {
                fprintf(stderr,"failed to increment module struc for pid = %d, tid = %d, ip = 0x%"PRIx64"\n",pid.pid,pid.tid,ip);
                err(1,"failed to increment module for sample");
                }

//	find mmap's for source & destination
//	determine module for principal process
//	for lbr_ret =1
//	increment rva record for source with destination for returns
//	increment rva record for destination with source for calls
#ifdef DBUG
	fprintf(stderr," return_filtered_return = %d\n",event_list[event_id].return_filtered_return);
#endif
	if(event_list[event_id].return_filtered_return != 1)return;
	lbr_ret = 1;
#ifdef DBUG
	fprintf(stderr," processing LBRs for filtered returns\n");
#endif
	for(i=0;i<num_lbr; i++)
		{
//	process the source = ip(return)
		local_mmap = bind_sample(pid.pid,lbr_data[i].source,this_time);
		if(local_mmap == NULL)
			{
#ifdef DBUGA
			fprintf(stderr," bind sample failed for source %d at 0x%"PRIx64"\n",i,lbr_data[i].source);
#endif
			continue;
			}
		if(local_mmap->principal_process == NULL)principal_process = find_principal_process(local_mmap);
		if(local_mmap->this_module == NULL)this_module = bind_mmap(local_mmap);
//	process the destination (call site + 1 instructions)
		target_mmap = bind_sample(pid.pid,lbr_data[i].destination,this_time);
		
		if(target_mmap == NULL)
			{
#ifdef DBUGA
			fprintf(stderr," bind sample failed for destination %d at 0x%"PRIx64"\n",i,lbr_data[i].destination);
#endif
			continue;
			}
		if(target_mmap->principal_process == NULL)principal_process = find_principal_process(target_mmap);
		if(target_mmap->this_module == NULL)this_module = bind_mmap(target_mmap);
		ret = increment_return(local_mmap, lbr_data[i].source, lbr_data[i].destination, target_mmap);
		ret = increment_call_site(local_mmap, lbr_data[i].source, lbr_data[i].destination, target_mmap);
		}
#endif
	free(lbr_data);
}

static void
display_mmap(bufdesc_t *desc, struct perf_event_header *ehdr)
{
/*
	struct {
		uint32_t pid, tid;
		uint64_t addr;
		uint64_t len;
		uint64_t pgoff;
	} mm;
*/
	mm_data mm;
	char *filename = NULL;
	size_t sz;
	int ret;

        mm_struc_ptr local_mm;
        process_struc_ptr this_process;

        local_mm = &mm;
        num_mmap++;


	ret = read_buffer(desc, &mm, sizeof(mm));
	if (ret)
		errx(1, "cannot read mmap data");

	sz = ehdr->size - sizeof(mm) - sizeof(*ehdr);
	filename = malloc(sz);
	if (!filename)
		err(1, "cannot allocate memory for mmap filename len=%zu", sz);

	ret = read_buffer(desc, filename, sz);
	if (ret)
		err(1, "cannot read mmap filename");

#ifdef DBUG
	fprintf(stderr,"MMAP: PID:%d TID:%d ADDR:0x%"PRIx64" LEN:0x%"PRIx64" PGOFF:0x%"PRIx64" FILE:%s\n",
		mm.pid,
		mm.tid,
		mm.addr,
		mm.len,
		mm.pgoff,
		filename);
#endif

#ifdef ANALYZE
        previous_mmap = insert_mmap(local_mm, filename,this_time);
#endif

#ifndef ANALYZE
	free(filename);
#endif
}

/*
 * layout:
 *
 * id: a unique identifier for each event. Used to tag
 * samples so they can be correlated to an event. If event
 * is attached to multiple threads or CPU, then perf_file_attr
 * may point to multiple IDs. One per file descriptor returned
 * by perf_event_open().
 *
 * attr: a verabtim copy of what was passed to the
 * perf_event_open() syscall, i.e., description of the
 * event to measure and sampling options.
 *
 * By extracting ID from PERF_RECORD_SAMPLE (assuming it's there),
 * one can get to the corresponding attr struct (reverse looking).
 *
 * The perf_file_attr section is reached via the file
 * header and hdr.attrs.offset.
 *
 * ---------------------
 *  perf_file_attr_1
 *        attr
 *        ids.offset -------> ----
 *        ids.size = 16       id1
 *                            ----
 * ---------------------      id2
 *  perf_file_attr_2          ---- 
 * ---------------------
 *  ...
 * ---------------------
 *  perf_file_attr_n
 * ---------------------
 */
static void
read_attrs(bufdesc_t *desc, struct perf_file_header *hdr)
{
	struct perf_file_attr f_attr;
	uint64_t id;
	int nr, i, j,ret;

        if (hdr->attr_size == 0)
                err(1, "hdr->attr_size=0 error\n");

	nr_attrs = hdr->attrs.size / hdr->attr_size;
	
	/*
	 * use calloc to ensure all fields are zeroed
	 * as we may not read sizeof() bytes worth of data
	 * from file
	 */
	attrs = calloc(nr_attrs, sizeof(*attrs));
	if (!attrs)
		err(1, "cannot allocate memory for attrs");

	desc->cur.pos = hdr->attrs.offset;

	for (i = 0; i < nr_attrs; i++) {
		ret = read_attr_from_file(desc, attrs+i);
		if (ret)
			errx(1, "cannot read file_attr");

		nr_ids += attrs[i].ids.size / sizeof(id);
#ifdef DBUGA
                fprintf(stderr," first loop attrs = %d, ids_size = %ld \n",i,attrs[i].ids.size);
                fprintf(stderr," attrs contents type = %d. size = %d, config = 0x%"PRIx64", period = %"PRIu64", sample_type = %"PRIu64", read_format = %"PRIu64"\n",attrs[i].attr.type,attrs[i].attr.size,attrs[i].attr.config,attrs[i].attr.sample.sample_period,attrs[i].attr.sample_type,attrs[i].attr.read_format);
                fprintf(stderr,"  wakeup events = %d, bp_type = %d\n",attrs[i].attr.wakeup.wakeup_events,attrs[i].attr.bp_type);
                fprintf(stderr,"  bp1.bp_addr = 0x%"PRIx64",bp1.config1 = 0x%"PRIx64", bp2.bp_len = %"PRIu64",bp2.config2 = 0x%"PRIx64"\n",attrs[i].attr.bp1.bp_addr,attrs[i].attr.bp1.config1,attrs[i].attr.bp2.bp_len,attrs[i].attr.bp2.config2);
#endif

                /*
                 * can only be one otherwise we have a chicken and egg problem
                 * in display_sample: we need the event_id to get to sample_type
                 * but the event_id is burried inside the body of a sample.
                 *
                 * for now perf applies the same sample_type to all events so
                 * that's fine
                 */

		if (!desc->sample_type)
			desc->sample_type = attrs[i].attr.sample_type;
		else if (desc->sample_type != attrs[i].attr.sample_type)
			errx(1, "profile contains event with different sample_type, cannot handle that...");
	}

	event_ids = malloc(nr_ids * sizeof(*event_ids));
	if (!event_ids)
		err(1, "cannot allocate memory for event_ids");

	for (i = j = 0; i < nr_attrs; i++) {
		desc->cur.pos = attrs[i].ids.offset;
		nr = j + attrs[i].ids.size / sizeof(id);
		for (; j < nr; j++) {
			raw_read_buffer(desc, &id, sizeof(id));
			event_ids[j].id = id;
			event_ids[j].attr_id = i;
		}
	}
#ifdef DBUG
	fprintf(stderr,"nr_attrs=%d nr_ids=%d\n", nr_attrs, nr_ids);
#endif
	for (i=0; i < nr_ids; i++) {

#ifdef DBUG
		fprintf(stderr,"ID:%"PRIu64" cfg=0x%"PRIx64" sample_type=0x%"PRIx64" sample_id_all=%d\n",
			event_ids[i].id,
			attrs[event_ids[i].attr_id].attr.config,
			attrs[event_ids[i].attr_id].attr.sample_type,
			attrs[event_ids[i].attr_id].attr.sample_id_all);
#endif

		if (attrs[event_ids[i].attr_id].attr.sample_id_all)
			desc->sample_id_all = 1;
	}

#ifdef ANALYZE
//comment out all this and use the event description records with the names
//        global_attrs = attrs;
//        global_event_ids = event_ids;

//        insert_event_descriptions(nr_attrs,nr_ids, attrs,event_ids);
//      fprintf(stderr," returned from insert_event_description\n");
//      initialize kernel process and thread since we will not get any comm records for this
#endif

	desc->cur.pos = desc->data.pos;
}

/*
 * for piped data, the event attributes (perf_evnet_attr + event_ids) are
 * scattered in the perf.data file therefore we harvest them as we go,
 * re-allocing attrs and event_ids along the way
 */
static void
read_attr_from_pipe(bufdesc_t *desc, struct perf_event_header *ehdr)
{
        struct perf_event_attr *attr;
        void *addr;
        int i, n;
        size_t sz, total_sz;

        nr_attrs++;
        attrs = realloc(attrs, nr_attrs * sizeof(*attrs));
        if (!attrs)
                err(1, "cannot allocate memory for piped attrs nr_attrs=%d", nr_attrs);

        attr = &attrs[nr_attrs - 1].attr;

        /* clear the new entry */
        memset(attr, 0, sizeof(*attr));

        /* hdr->size may be rounded up to 64 multiple */
        total_sz = ehdr->size - sizeof(*ehdr);

        raw_read_buffer(desc, attr, PERF_ATTR_SIZE_VER0);

#ifdef DBUG
        fprintf(stderr,"on file sizeof(perf_event_attr)=%d ABI0=%d\n", attr->size, PERF_ATTR_SIZE_VER0);
        fprintf(stderr,"reader sizeof(perf_event_attr)=%zu\n", sizeof(*attr));
        fprintf(stderr,"attr.type=%d attr.config=0x%"PRIx64" attr.period=%"PRIu64"\n",
                attr->type,
                attr->config,
                attr->sample.sample_period);
#endif

        /*
         * size = 0 <=> attr->size PERF_ATTR_SIZE_VER0
         */
        if (attr->size == 0 || attr->size == PERF_ATTR_SIZE_VER0) {
#ifdef DBUG
                fprintf(stderr,"on file sizeof(perf_event_attr) = ABI0 (%d bytes)\n", PERF_ATTR_SIZE_VER0);
#endif
                goto read_ids;
        }

        sz = attr->size;
        if (sz > sizeof(*attr)) {
                sz = sizeof(*attr);
                warnx("perf.data file contains a newer revision (%zu bytes) of perf_event_attr, some field will be ignored", sz - PERF_ATTR_SIZE_VER0);
        }

        sz -= PERF_ATTR_SIZE_VER0;
        total_sz -= PERF_ATTR_SIZE_VER0;

        if (sz) {
                /* go to void * for pointer arithmetic */
                addr = attr;
                addr += PERF_ATTR_SIZE_VER0;
#ifdef DBUG
                fprintf(stderr,"read %zu extra bytes we know about for perf_event_attr\n", sz);
#endif
                /*
                 * read the extra stuff we know about
                 */
                raw_read_buffer(desc, addr, sz);
                total_sz -= sz;

        }
        /* skip what we don't know about */
        if (attr->size > sizeof(*attr)) {
                sz = attr->size - sizeof(*attr);
                raw_skip_buffer(desc, sz);
                total_sz -= sz;
        }
read_ids:
        /*
         * can only be one otherwise we have a chicken and egg problem
         * in display_sample: we need the event_id to get to sample_type
         * but the event_id is burried inside the body of a sample.
         *
         * for now perf applies the same sample_type to all events so
         * that's fine
         */
        if (!desc->sample_type)
                desc->sample_type = attr->sample_type;
        else if (desc->sample_type != attr->sample_type)
                errx(1, "profile contains event with different sample_type, cannot handle that...");

#ifdef DBUG
        fprintf(stderr,"SAMPLE_TYPE=0x%"PRIx64"\n", attr->sample_type);
#endif

        if (nr_attrs > 1 && desc->sample_id_all != attr->sample_id_all)
                errx(1, "profile contains event with different sample_id_all fields, cannot handle that...");

        desc->sample_id_all = attr->sample_id_all;

        if (nr_attrs > 1 && desc->sample_id_all != attr->sample_id_all)
                errx(1, "profile contains event with different sample_id_all fields, cannot handle that...");

        desc->sample_id_all = attr->sample_id_all;

        n = total_sz / sizeof(uint64_t);

        event_ids = realloc(event_ids, (nr_ids+n) * sizeof(*event_ids));
        if (!event_ids)
                err(1, "cannot allocate memory for event_ids");

        for (i = 0 ; i < n; i++, nr_ids++) {
                uint64_t id;

                raw_read_buffer(desc, &id, sizeof(id));

                event_ids[nr_ids].id = id;
                event_ids[nr_ids].attr_id = nr_attrs - 1;

#ifdef DBUG
                fprintf(stderr,"ID:%"PRIu64" cfg=0x%"PRIx64" sample_type=0x%"PRIx64" sample_id_all=%d\n",
                        event_ids[nr_ids].id,
                        attrs[nr_attrs - 1].attr.config,
                        attrs[nr_attrs - 1].attr.sample_type,
                        attrs[nr_attrs - 1].attr.sample_id_all);
#endif
        }
}

static void
display_header_attr(bufdesc_t *desc, struct perf_event_header *ehdr)
{
        read_attr_from_pipe(desc, ehdr);
}

static void
display_event_type(bufdesc_t *desc, struct perf_event_header *ehdr)
{
        struct perf_trace_event_type ev;
        int ret, sz;

        sz = ehdr->size - sizeof(*ehdr) - sizeof(ev.event_id);
        if (sz <= 0)
                errx(1, "invalid size for PERF_RECORD_HEADER_ATTR");

        if (sz > MAX_EVENT_NAME)
                errx(1, "size %d too big for PERF_RECORD_HEADER_ATTR", sz);

#ifdef DBUG
        fprintf(stderr,"ehdr.size=%d ev=%zu sz=%d\n", ehdr->size, sizeof(ev), sz);
#endif

        ret = read_buffer(desc, &ev.event_id, sizeof(ev.event_id));
        if (ret)
                errx(1, "cannot read event type");

        ret = read_buffer(desc, ev.name, sz);
        if (ret)
                errx(1, "cannot read event type");

#ifdef DBUG
        fprintf(stderr,"EVENT_TYPE: ID:0x%"PRIx64" NAME:%s\n",
                ev.event_id,
                ev.name);
#endif
}
static void
display_tracing(bufdesc_t *desc, struct perf_event_header *ehdr)
{
        struct tracing_data_event d;

        raw_read_buffer(desc, &d, sizeof(d));

#ifdef DBUG
        fprintf(stderr,"TRACING: SIZE:%d (skipped)\n", d.size);
#endif
        skip_buffer(desc, d.size);
}

static void
read_one_buildid(bufdesc_t *desc, struct perf_event_header *ehdr)
{
        struct build_id_event_type b;
        int i, len;
        char *str;

        raw_read_buffer(desc, &b, sizeof(b));

        len = ehdr->size - sizeof(b) - sizeof(*ehdr);
        if (len <= 0)
                errx(1, "build_id event len < 0");

        str = malloc(len);
        if (!str)
                err(1, "cannot allocate memory for build id string size=%d", len);

#ifdef DBUG
        fprintf(stderr,"PID:%d ", b.pid);
#endif
        raw_read_buffer(desc, str, len);
#ifdef DBUG
        for (i = 0; i < BUILD_ID_SIZE; i++) {
                printf("%02x", b.build_id[i]);
        }
        printf(" %s\n", str);
#endif
        free(str);
}

static void
display_build_id(bufdesc_t *desc, struct perf_event_header *ehdr)
{
#ifdef DBUG
        fprintf(stderr,"BUILDID: ");
#endif
        read_one_buildid(desc, ehdr);
}

static void
display_finished_round(bufdesc_t *desc, struct perf_event_header *ehdr)
{
        /* This is just a marker record, no useful body */
#ifdef DBUG
        fprintf(stderr,"FINISHEDROUND\n");
#endif
        /* just in case there would be something to skip */
        skip_buffer(desc, ehdr->size - sizeof(*ehdr));
}

static void
display_feature(bufdesc_t *desc, struct perf_event_header *ehdr)
{
        int feat;

        feat = rec2feat[ehdr->type];
        if (feat == 0) {
                fprintf(stderr,"unhandled feature record type %d\n", ehdr->type);
                skip_buffer(desc, ehdr->size - sizeof(*ehdr));
                return;
        }
        (*read_feature[feat])(desc, NULL);
}

static record_ops_t record_ops[]={
	[PERF_RECORD_MMAP] 		= display_mmap,
	[PERF_RECORD_LOST] 		= display_lost,
	[PERF_RECORD_COMM] 		= display_comm,
	[PERF_RECORD_EXIT] 		= display_exit,
	[PERF_RECORD_THROTTLE]		= display_throttle,
	[PERF_RECORD_UNTHROTTLE]	= display_unthrottle,
	[PERF_RECORD_FORK]		= display_fork,
	[PERF_RECORD_READ]		= display_read,
	[PERF_RECORD_SAMPLE]		= display_sample,

        /* pseudo samples injected by perf-inject */
        [PERF_RECORD_HEADER_ATTR]         = display_header_attr,
        [PERF_RECORD_HEADER_EVENT_TYPE]   = display_event_type,
        [PERF_RECORD_HEADER_TRACING_DATA] = display_tracing,
        [PERF_RECORD_HEADER_BUILD_ID]     = display_build_id,
        [PERF_RECORD_FINISHED_ROUND]      = display_finished_round,
        [PERF_RECORD_HEADER_HOSTNAME]     = display_feature,
        [PERF_RECORD_HEADER_OSRELEASE]    = display_feature,
        [PERF_RECORD_HEADER_VERSION]      = display_feature,
        [PERF_RECORD_HEADER_ARCH]         = display_feature,
        [PERF_RECORD_HEADER_NRCPUS]       = display_feature,
        [PERF_RECORD_HEADER_CPUDESC]      = display_feature,
        [PERF_RECORD_HEADER_CPUID]        = display_feature,
        [PERF_RECORD_HEADER_TOTAL_MEM]    = display_feature,
        [PERF_RECORD_HEADER_CMDLINE]      = display_feature,
	[PERF_RECORD_HEADER_EVENT_DESC]   = display_feature,
	[PERF_RECORD_HEADER_CPU_TOPOLOGY] = display_feature,
        [PERF_RECORD_HEADER_NUMA_TOPOLOGY]= display_feature,

};
#define NUM_RECORD_OPS	(sizeof(record_ops))/sizeof(record_ops_t));

static void
parse(bufdesc_t *desc)
{
	struct perf_event_header ehdr;
	uint64_t opos;
	int ret;

	for(;;) {
		opos = desc->cur.pos;
		ret = read_buffer(desc, &ehdr, sizeof(ehdr));
		if (ret)
			return; /* nothing to read */

		//fprintf(stderr,"SAMPLE.TYPE:%d SAMPLE.SZ:%d\n", ehdr.type, ehdr.size);

                if (ehdr.type < PERF_RECORD_MMAP || ehdr.type >= PERF_RECORD_HEADER_MAX) {
                        printf("unknown sample type %d size=%d\n", ehdr.type, ehdr.size);
                        skip_buffer(desc, ehdr.size - sizeof(ehdr));
                        continue;
                }

                if (!record_ops[ehdr.type]) {
                        printf("unknown sample type %d size=%d\n", ehdr.type, ehdr.size);
                        skip_buffer(desc, ehdr.size - sizeof(ehdr));
                        continue;
                }

                record_ops[ehdr.type](desc, &ehdr);

		if ((desc->cur.pos - opos) != ehdr.size) {
#ifdef DBUG
			fprintf(stderr,"skipping unknown record extension of %"PRIu64" bytes\n", opos + ehdr.size - desc->cur.pos);
#endif
			skip_buffer(desc, opos + ehdr.size - desc->cur.pos);
		}
	}
}

static char *
raw_read_string(bufdesc_t *desc)
{
	char *str;
	int len;

	raw_read_buffer(desc, &len, sizeof(len));
	if (len < 0)
		err(1, "invalid event/hostname string len=%d", len);

	str = malloc(len);
	if (!str)
		err(1, "cannot allocate %d bytes for event/hostname string", len);

	raw_read_buffer(desc, str, len);

	return str;
}
/*
//comment this out as there is a new function earlier in the listing
static void
read_one_buildid(bufdesc_t *desc)
{
	struct build_id_event b;
	int i, len;
	char *str;

	raw_read_buffer(desc, &b, sizeof(b));

	len = b.header.size - sizeof(b);
	str = malloc(len);
	if (!str)
		{
		fprintf(stderr," malloc failed in read_one_buildid, len = %d, size = %d, sizeof(b) = %d\n",len,b.header.size,sizeof(b));
		err(1, "cannot allocate memory for build id string");
		}

	raw_read_buffer(desc, str, len);
	for (i = 0; i < BUILD_ID_SIZE; i++) {
#ifdef DBUG
		fprintf(stderr,"%02x", b.build_id[i]);
#endif
	}
#ifdef DBUG
	fprintf(stderr," %s\n", str);
#endif
	free(str);
}
*/
static void
read_buildids(bufdesc_t *desc, struct perf_file_header *hdr)
{
	struct perf_event_header ehdr;
	uint64_t end = desc->feat[HEADER_BUILD_ID].end;
	uint64_t pos = desc->cur.pos;

	while (pos < end) {
		raw_read_buffer(desc, &ehdr, sizeof(ehdr));
		read_one_buildid(desc, &ehdr);
		pos = desc->cur.pos;
	}
}

static void
read_hostname(bufdesc_t *desc, struct perf_file_header *hdr)
{
	char *str;

	str = raw_read_string(desc);
	if (!str)
		err(1, "cannot read hostname");

#ifdef DBUG
	fprintf(stderr,"Machine   : %s\n", str);
#endif

	free(str);

}

static void
read_osrelease(bufdesc_t *desc, struct perf_file_header *hdr)
{
	char *str;
	int len;

	str = raw_read_string(desc);
	if (!str)
		err(1, "cannot read os release");

#ifdef DBUG
	fprintf(stderr,"OS release: %s\n", str);
#endif

	free(str);

}

static void
read_arch(bufdesc_t *desc, struct perf_file_header *hdr)
{
	char *str;

	str = raw_read_string(desc);
	if (!str)
		err(1, "cannot read arch");

#ifdef DBUG
	fprintf(stderr,"Arch      : %s\n", str);
#endif

	arch = str;

//	free(str);

}

static void
read_cpudesc(bufdesc_t *desc, struct perf_file_header *hdr)
{
	char *str;

	str = raw_read_string(desc);
	if (!str)
		err(1, "cannot read arch");

#ifdef DBUG
	fprintf(stderr,"CPU Desc  : %s\n", str);
#endif

	cpu_desc = str;

//	free(str);
}

static void
read_cpuid(bufdesc_t *desc, struct perf_file_header *hdr)
{
        char *str, fam_str[10],model_str[10];
	int i,j,k,comma_count,cpu_len;
	j=0;
	k=0;
	comma_count = 0;
	family = 0;
	model = 0;

        str = raw_read_string(desc);
        if (!str)
                err(1, "cannot read arch");

#ifdef DBUG
        fprintf(stderr,"CPUID     : %s\n", str);
#endif

	cpu_len = strlen(str);
	for(i=0; i< cpu_len; i++)
		{
		if(str[i] == ',')comma_count++;
		if((comma_count == 1) && (str[i] != ','))
			{
			fam_str[j] = str[i];
			j++;
			}
		if((comma_count == 2) && (str[i] != ','))
			{
			model_str[k] = str[i];
			k++;
			}
		}
	fam_str[j] = '\0';
	model_str[k] = '\0';
	if(j != 0)family = atoi(fam_str);
	if(k != 0)model = atoi(model_str);
//#ifdef DBUG
	fprintf(stderr," family = %d, model = %d\n",family,model);
//#endif
        free(str);
}

static void
read_version(bufdesc_t *desc, struct perf_file_header *hdr)
{
	char *str;

	str = raw_read_string(desc);
	if (!str)
		err(1, "cannot read version");

#ifdef DBUG
	fprintf(stderr,"Perf Version: %s\n", str);
#endif

	free(str);
}

static void
read_nrcpus(bufdesc_t *desc, struct perf_file_header *hdr)
{
	size_t old_pos = desc->cur.pos;
	struct {
		int nconf;
		int nonln;
	} nrcpus;

	raw_read_buffer(desc, &nrcpus, sizeof(nrcpus));

#ifdef DBUG
	fprintf(stderr,"CPU config: %d\n", nrcpus.nconf);
	fprintf(stderr,"CPU online: %d\n", nrcpus.nonln);
#endif
}

static void
read_event_desc(bufdesc_t *desc, struct perf_file_header *hdr)
{
	struct perf_event_attr attr;
	size_t old_pos = desc->cur.pos;
	uint64_t id, max_id = 0;
	char *str, *buf;
	int i, j, k, len, last, nre, nri, sz, msz;
	int period_test;
	int previous_nri = -1;
	void* ret_set;

	fprintf(stderr," max_id = %ld, min_event_id = %ld\n",max_id, min_event_id);
	/* number of events */
	raw_read_buffer(desc, &nre, sizeof(nre));

	/* size of perf_event_attr in the file */
	raw_read_buffer(desc, &sz, sizeof(sz));

	buf = malloc(sz);
	if (!buf)
		return;

	/*
	 * adjust copied size based on relative size of
	 */
	msz = sizeof(attr);
	ret_set = memset((void*)&attr,0,msz);
	
	if (sz < msz)
		msz = sz;

	event_list = (event_name_struc_ptr) malloc(nre*sizeof(event_name_data));

	if(event_list == NULL)
		{
		fprintf(stderr,"failed to malloc event_list in read_event_desc\n");
		err(1,"failed to malloc event_list in read_event_desc");
		}

	global_attrs = (event_attr_ptr) malloc(nre*sizeof(event_attr_data));
	if(global_attrs == NULL)
		{
		fprintf(stderr,"failed to malloc global_attrs in read_event_desc, nre = %d\n",nre);
		err(1,"failed to malloc global_attrs in read_event_desc");
		}

	for (i = 0; i < nre; i++) {

		/* attr for the event */
		raw_read_buffer(desc, buf, sz);

		memcpy(&attr, buf, msz);

		/* number of id */
		raw_read_buffer(desc, &nri, sizeof(nri));

//	start constructing the global_attrs entry
		memcpy(&global_attrs[i].attr, buf, msz);
		global_attrs[i].nr_ids = nri;
		global_attrs[i].ids = (uint64_t *)malloc(nri*sizeof(uint64_t));
		if(global_attrs[i].ids == NULL)
			{
			fprintf(stderr,"mailed to malloc ids array for event %d in read_event_desc\n",i);
			err(1," malloc of ids array failed in read_event_desc");
			}

		if(i == 0)previous_nri = nri;
		if(i > 0)
			{
			if(nri != previous_nri)
				{
				fprintf(stderr," event %d does not have the same number of id's = %d as the previous event did = %d\n",
					i,nri,previous_nri);
				err(1,"inconsistent event id count in read_event_desc");
				}
			}
		str = raw_read_string(desc);

//#ifdef DBUG
		fprintf(stderr,"# EVENT :name = %s, nri = %d ", str, nri);
//#endif

//		free(str);
#ifdef DBUG
		fprintf(stderr,"type = %d, config = 0x%"PRIx64", config1 = 0x%"PRIx64", config2 = 0x%"PRIx64,
			attr.type,
			attr.config,
			attr.bp1.config1,
			attr.bp2.config2);

		fprintf(stderr,", excl_usr = %d, excl_kern = %d\n",
			attr.exclude_user,
			attr.exclude_kernel);
		if(attr.branch_sample_type)
			fprintf(stderr,"branch_sample_type = 0x%"PRIx64"\n",attr.branch_sample_type);
#endif
//#ifdef DBUG
		if (nri)
			fprintf(stderr,",  id = {");
//#endif

		for (j = 0 ; j < nri; j++) {
			raw_read_buffer(desc, &id, sizeof(id));
			global_attrs[i].ids[j] = id;
			if(id > max_id)
				{
				max_id = id;
				max_id_event = i;
				}
			if(id < min_event_id)
				{
				min_event_id = id;
				min_id_event = i;
				}
//#ifdef DBUG
			if (j)
				fputc(',',stderr);
			fprintf(stderr," %"PRIu64, id);
//#endif
		}
//#ifdef DBUG
		if (nri && j == nri)
			fprintf(stderr," }\n");
//#endif

//	process event_desc, create map of event IDs to event numbers and call init_order

		global_attrs[i].name = str;
		len = strlen(str);
		period_test = 0;
		for(k=0; k<len-7; k++)
			{
			if((str[k] == ':') && (str[k+1] == 'p') && (str[k+2] =='e') && (str[k+3] == 'r') && (str[k+4] =='i') 
				&& (str[k+5] == 'o') && (str[k+6] == 'd') && (str[k+7] == '='))
				{
				period_test = 1;
				last = k;
				break;
				}
			}
		if(period_test == 0)
			{
			fprintf(stderr," event does not have period, data cannot be analyzed, event = %s\n",str);
			err(1,"from read_event_desc, bad event programming during collection, not analyzable, fixed periods are required\n");
			}

		event_list[i].name = (char *) malloc((last+1)*sizeof(char));
		if(event_list[i].name == NULL)
			{
			fprintf(stderr,"malloc of event name failed in read_event_desc for event = %s\n",str);
			err(1,"malloc failed in read_event_desc");
			}
		for(k=0; k<last; k++)event_list[i].name[k] = str[k];
		event_list[i].name[last] = '\0';
		event_list[i].config = attr.config;
		event_list[i].period = attr.sample.sample_period;
		event_list[i].branch_sample_type = attr.branch_sample_type;
		event_list[i].return_filtered_return = 0;
		if((strcasecmp(event_list[i].name,return_event) == 0) &&
			(attr.branch_sample_type ==  PERF_SAMPLE_BRANCH_ANY_RETURN))event_list[i].return_filtered_return = 1;

#ifdef DBUG
		fprintf(stderr," event_list[%d] name = %s, period = %ld, config = 0x%"PRIx64"\n",
			i,event_list[i].name,event_list[i].period,event_list[i].config);
		fprintf(stderr," branch filters: branch_sample_type = 0x%"PRIx64", return_filtered = %d\n",
			event_list[i].branch_sample_type,event_list[i].return_filtered_return);
#endif

	}
#ifdef DBUG
	fprintf(stderr," max_id = %ld, min_event_id = %ld\n",max_id, min_event_id);
#endif
#ifdef ANALYZE
	num_events = nre;
	id_array = (int*)malloc((int)(max_id - min_event_id + 1)*sizeof(int));
	if(id_array == NULL)
		{
		fprintf(stderr,"failed to malloc id_array, max_id = %ld, min_event_id = %ld\n",max_id,min_event_id);
		err(1,"id_array malloc failed in read_event_desc");
		}
	fprintf(stderr," max_id = %ld, min_event_id = %ld\n",max_id, min_event_id);
	fprintf(stderr,"num_events = %d, nri = %d, min_id_event = %d, max_id_event = %d\n",nre,nri,min_id_event,max_id_event); 
	for(i=0; i< nre; i++)
		{
		fprintf(stderr,"event_name = %s, first ids = %ld, last ids = %ld\n",event_list[i].name,global_attrs[i].ids[0],global_attrs[i].ids[nri-1]);
		for(j=0; j<global_attrs[i].nr_ids; j++)
			id_array[(int)(global_attrs[i].ids[j] - min_event_id)] = i;
		}

//	insert_event_names(nre,name_list);
#endif
}

static void
read_cmdline(bufdesc_t *desc, struct perf_file_header *hdr)
{
	char *str;
	int i, argc;
	int previous_b, len;

	previous_b = 0;

	/*
	 * note that there is NO argv[x] = NULL termination
	 * record in the perf.data file
	 */
	raw_read_buffer(desc, &argc, sizeof(argc));
	for (i = 0 ; i < argc; i++) {
		str = raw_read_string(desc);
#ifdef DBUG
		fprintf(stderr,"argv[%d] = %s\n", i, str);
#endif

		free(str);
	}
}

static void
read_cpu_topology(bufdesc_t *desc, struct perf_file_header *hdr)
{
        uint32_t i, nr, cpu, socket_count, core_count,num_col;
	int len,j;
        char *str;

	socket_count = 0;
	core_count = 0;

        raw_read_buffer(desc, &nr, sizeof(nr));
	socket_count = nr;
	fprintf(stderr,"first value of nr = %d\n",nr);
        for (i = 0 ; i < nr; i++) {
                str = raw_read_string(desc);
#ifdef DBUG
                fprintf(stderr,"Core  siblings: %s\n", str);
#endif
                free(str);
        }
        raw_read_buffer(desc, &nr, sizeof(nr));
	core_count = nr;
	fprintf(stderr,"second value of nr = %d\n",nr);
        for (i = 0 ; i < nr; i++) {
                str = raw_read_string(desc);
                fprintf(stderr,"Thread siblings: %s\n", str);
		len = strlen(str);
		for(j = 0; j<len; j++)
			if(str[j] == ',')core_count++;
                fprintf(stderr,"Thread siblings: %s\n", str);
#ifdef DBUG
                fprintf(stderr,"Thread siblings: %s\n", str);
#endif
                free(str);
        }
#ifdef ANALYZE
	num_cores = core_count;
	num_sockets = socket_count;

	fprintf(stderr," num_cores = %d, num_sockets = %d\n",num_cores,num_sockets);

	init_order();
	num_branch = global_event_order->num_branch;
	num_sub_branch = global_event_order->num_sub_branch;
	num_derived = global_event_order->num_derived;
//      create global_sample_count array
        global_sample_count = (int*) malloc((num_events*(num_cores + num_sockets +1) + num_branch + num_sub_branch + num_derived + 1)*sizeof(int));
        if(global_sample_count == NULL)
                {
                fprintf(stderr, " failed to malloc array for global_sample_count\n");
                err(1," failed to malloc global_sample_count");
                }
        memset((void*) global_sample_count, 0, (size_t) 
		(num_events*(num_cores+num_sockets+1) + num_branch + num_sub_branch + num_derived + 1)*sizeof(int) );

	num_col = num_events+global_event_order->num_branch + global_event_order->num_sub_branch +global_event_order->num_derived + 1;
	fprintf(stderr,"initialization: global_sample_count totals  ");
	for(i=0; i< num_col; i++)fprintf(stderr," %d,",global_sample_count[num_events*(num_cores+num_sockets) + i]);
	fprintf(stderr,"\n");

//      create global_multiplex_correction array

        global_multiplex_correction = (double*) malloc(
		(num_events*(num_cores + num_sockets +1) + num_branch + num_sub_branch + num_derived + 1)*sizeof(double));
        if(global_multiplex_correction == NULL)
                {
                fprintf(stderr, " failed to malloc array for global_multiplex_correction\n");
                err(1," failed to malloc global_multiplex_correction");
                }
        for(i=0; i < (num_events*(num_cores+num_sockets+1) + num_branch + num_sub_branch + num_derived + 1); i++)
		global_multiplex_correction[i] = 1.0;
#endif
}

static void
read_numa_topology(bufdesc_t *desc, struct perf_file_header *hdr)
{
        uint32_t i, nr, n;
        uint64_t mem_total, mem_free;
        char *str;

        raw_read_buffer(desc, &nr, sizeof(nr));

        for (i = 0 ; i < nr; i++) {
                raw_read_buffer(desc, &n, sizeof(n));
                raw_read_buffer(desc, &mem_total, sizeof(mem_total));
                raw_read_buffer(desc, &mem_free, sizeof(mem_free));
                str = raw_read_string(desc);

#ifdef DBUG
                fprintf(stderr,"Node%u meminfo : total = %"PRIu64" kB, free = %"PRIu64" kB\n",
                        n,
                        mem_total,
                        mem_free);

                fprintf(stderr,"Node%u cpulist : %s\n", n, str);
#endif
                free(str);

        }
}


static int
read_attr_from_file(bufdesc_t *desc, struct perf_file_attr *attrs)
{
	struct perf_event_attr *attr = &attrs->attr;
	void *addr;
	int ret;
	size_t sz;

	/* read the base ABI struct, any attr struct is guaranteed
	 * to be at least that big
	 */
	raw_read_buffer(desc, attr, PERF_ATTR_SIZE_VER0);

#ifdef DBUG
	fprintf(stderr,"on file sizeof(perf_event_attr)=%d\n", attr->size);
	fprintf(stderr,"reader sizeof(perf_event_attr)=%zu\n", sizeof(*attr));
	fprintf(stderr,"attr.type=%d attr.config=0x%"PRIx64" attr.period=%"PRIu64"\n",
                attr->type,
                attr->config,
                attr->sample.sample_period);
#endif
	/*
	 * size = 0 <=> attr->size PERF_ATTR_SIZE_VER0
	 */
	if (attr->size == 0 || attr->size == PERF_ATTR_SIZE_VER0) {
#ifdef DBUG
		fprintf(stderr,"on file sizeof(perf_event_attr) = ABI0 (%d bytes)\n", attr->size, PERF_ATTR_SIZE_VER0);
#endif
		return 0;
	}

	sz = attr->size;
	if (sz > sizeof(*attr)) {
		sz = sizeof(*attr);
		warnx("perf.data file contains a newer revision (%zu bytes) of perf_event_attr, some field will be ignored", sz - PERF_ATTR_SIZE_VER0);
	}

	sz -= PERF_ATTR_SIZE_VER0;
	if (sz) {
		/* go to void * for pointer arithmetic */
		addr = attr;
		addr += PERF_ATTR_SIZE_VER0;
#ifdef DBUG
		fprintf(stderr,"read %zu extra bytes we know about for perf_event_attr\n", sz);
#endif
		/*
		 * read the extra stuff we know about
		 */
		raw_read_buffer(desc, addr, sz);
	}
	/* skip what we don't know about */
	if (attr->size > sizeof(*attr)) {
		sz = attr->size - sizeof(*attr);
		raw_skip_buffer(desc, sz);
	}
	/*
	 * sanity check (assume no padding on file)
	 */
	if (offsetof(struct perf_file_attr, ids) != sizeof(*attr)) {
		errx(1, "cannot read perf_file_attr, incorrect padding");
	}
	/* read the file_section */
	raw_read_buffer(desc, &attrs->ids, sizeof(struct perf_file_section));
	return 0;
}

static void
read_total_mem(bufdesc_t *desc, struct perf_file_header *hdr)
{
	uint64_t total_mem;

	raw_read_buffer(desc, &total_mem, sizeof(total_mem));

#ifdef DBUG
	fprintf(stderr,"Total memory: %"PRIu64" kB\n", total_mem);
#endif
}


static void (*read_feature[HEADER_LAST_FEATURE])(bufdesc_t *, struct perf_file_header *)={
	[HEADER_BUILD_ID] = read_buildids,
	[HEADER_HOSTNAME] = read_hostname,
	[HEADER_OSRELEASE] = read_osrelease,
	[HEADER_VERSION] = read_version,
	[HEADER_ARCH] = read_arch,
	[HEADER_NRCPUS] = read_nrcpus,
	[HEADER_CPUDESC] = read_cpudesc,
	[HEADER_CPUID] = read_cpuid,
	[HEADER_TOTAL_MEM] = read_total_mem,
	[HEADER_CMDLINE] = read_cmdline,
	[HEADER_EVENT_DESC] = read_event_desc,
	[HEADER_CPU_TOPOLOGY] = read_cpu_topology,
	[HEADER_NUMA_TOPOLOGY] = read_numa_topology,
};

static void
read_feature_bits(bufdesc_t *desc, struct perf_file_header *hdr)
{
	struct perf_file_section feat_sec;
	uint64_t mask = hdr->adds_features[0];
	uint64_t pos;
	int i;

	/* feature bits are after data section */
	pos = hdr->data.offset + hdr->data.size;

	/*
	 * would need a proper implementation of bitmasks
	 */
	if (HEADER_LAST_FEATURE > (sizeof(mask)<<3))
		err(1, "reader can only handle first 64 features\n");

	for (i = 0 ; i < HEADER_LAST_FEATURE; i++) {

		if (!(mask &  (1ULL << i)))
			continue;


		/* extract feature desc */
		desc->cur.pos = pos;
		raw_read_buffer(desc, &feat_sec, sizeof(feat_sec));

		desc->feat[i].pos = feat_sec.offset;
		desc->feat[i].end = feat_sec.offset + feat_sec.size;

		pos += sizeof(struct perf_file_section);

		/* point to beginning of feature */
		desc->cur.pos = feat_sec.offset;

		if (read_feature[i])
			read_feature[i](desc, hdr);
		else
			fprintf(stderr,"contains feature %d but unspported by reader\n", i);
	}
}

static int
validate_magic(uint64_t *magic)
{
        int i;
	int ret;

        fprintf(stderr, "on file magic string:\n");

        for (i = 0; i < 8; i++) {
                char *s = (char *)magic;
                fprintf(stderr, "M[%d]=%d %c\n", i, s[i], s[i]);
        }

        ret = memcmp(magic, __perf_magic, sizeof(*magic));
        if (!ret)
                return 1;

        ret = memcmp(magic, &__perf_magic2, sizeof(*magic));
        if (!ret)
                return 1;

        ret = memcmp(magic, &__perf_magic2_sw, sizeof(*magic));
        if (!ret)
                warnx("reader does not yet support heterogeneous endianness\n");

        return 0;

}

static void
read_file_header(bufdesc_t *desc)
{
	struct perf_file_header hdr;
	struct stat stat;
	int ret;

#ifdef DBUG
	fprintf(stderr,"NON-PIPED FILE DETECTED\n");
#endif

	ret = fstat(desc->fd, &stat);
	if (ret)
		err(1, "cannot stat data file");

	desc->cur.end = stat.st_size;

	raw_read_buffer(desc, &hdr, sizeof(hdr));

#ifdef DBUG
	fprintf(stderr,"file header size: %"PRIu64"\n", hdr.size);
#endif
	/*
	 * XXX: assume same endianess (not bswap64())
	 */
	if (hdr.size != sizeof(hdr))
		errx(1, "perf_file_header struct has unexpected size %"PRIu64, hdr.size);

#ifdef DBUG
	fprintf(stderr,"size: %"PRIu64" attr_size: %"PRIu64"\n", hdr.size, hdr.attr_size);
	fprintf(stderr,"attrs.offset: %"PRIu64" attrs.size: %"PRIu64"\n", hdr.attrs.offset, hdr.attrs.size);
	fprintf(stderr,"data.offset: %"PRIu64" data.size: %"PRIu64"\n", hdr.data.offset, hdr.data.size);
	fprintf(stderr,"event_types.offset: %"PRIu64" event_types.size: %"PRIu64"\n", hdr.event_types.offset, hdr.event_types.size);
#endif

	if (hdr.attrs.size)
		read_attrs(desc, &hdr);

	desc->data.pos = hdr.data.offset;
	desc->data.end = hdr.data.offset + hdr.data.size;

	read_feature_bits(desc, &hdr);

	desc->cur.pos = desc->data.pos;
}

static void
read_pipe_header(bufdesc_t *desc)
{
        struct perf_pipe_file_header hdr;
        struct stat stat;
        int ret;

#ifdef DBUG
        fprintf(stderr,"PIPED FILE DETECTED\n");
#endif
        ret = fstat(desc->fd, &stat);
        if (ret)
                err(1, "cannot stat data file");

        desc->cur.end = stat.st_size;

        raw_read_buffer(desc, &hdr, sizeof(hdr));

#ifdef DBUG
        fprintf(stderr,"file header size: %"PRIu64"\n", hdr.size);
#endif

        desc->data.pos = sizeof(hdr);
        desc->data.end = desc->cur.end;

        desc->cur.pos = desc->data.pos;
}

static int
detect_piped_file(bufdesc_t *desc)
{
        /* same layout as file_header for 1st two fields */
        struct perf_pipe_file_header hdr;
        struct stat stat;
        bufdesc_t d = *desc;
        int ret;

        ret = fstat(desc->fd, &stat);
        if (ret)
                err(1, "cannot stat data file");

        d.cur.end = stat.st_size;

        d.fd = dup(desc->fd);
        if (!d.fd)
                err(1, "cannot duplicate file descriptor");

        raw_read_buffer(&d, &hdr, sizeof(hdr));

        if (!validate_magic(&hdr.magic))
                errx(1, "not a perf.data file");

        /*
         * heuristic: detect pipe mode based on the size of the
         * on file header. Both file and pipe mode have the same
         * layout for the first 2 fields: magic, size. Use the
         * size field to determine file type.
         *
         * XXX: does not work when host and file have different endianess
         * but endianess ought to be detected via the magic number
         */
        if (hdr.size == sizeof(hdr))
                ret = 1;

        close(d.fd);

        return ret;
}

/*
 *  0: success
 * -1: missing PERF_SAMPLE_READ
 * -2: at least one event missing PERF_FORMAT_TOTAL_TIME_ENABLED
 * -3: at least one event missing PERF_FORMAT_TOTAL_TIME_RUNNING
 * -4: missing event description in header
 */

static int
valid4gooda(bufdesc_t *desc)
{
        uint64_t fmt;
        int i;

        /*
         * check multiplexing timing correction for scaling
         * needs:
         * - sample_type & PERF_SAMPLE_READ
         * - read_format & PERF_FORMAT_TOTAL_TIME_ENABLED
         * - read_format & PERF_FORMAT_TOTAL_TIME_RUNNING)
         */
        if (!(desc->sample_type & PERF_SAMPLE_READ))
                return -1;

        for (i = 0; i < nr_ids; i++) {
                fmt = attrs[event_ids[i].attr_id].attr.read_format;
                if (!(fmt & PERF_FORMAT_TOTAL_TIME_ENABLED))
                        return -2;
                if (!(fmt & PERF_FORMAT_TOTAL_TIME_RUNNING))
                        return -3;
        }

        /*
         * check for meta-data headers
         * needs:
         * - HEADER_EVENT_DESC
         */
        if (!desc->feat[HEADER_EVENT_DESC].pos)
                return -4;

        return 0;
}

static const char *gooda_check_results[]={
        "Yes",
        "No, missing PERF_SAMPLE_READ",
        "No, missing PERF_FORMAT_TOTAL_TIME_ENABLED",
        "No, missing PERF_FORMAT_TOTAL_TIME_RUNNING",
        "No, missing HEADER_EVENT_DESC",
};
#define NUM_GOODA_RESULTS (sizeof(gooda_check_results)/sizeof(const char *))

static void
check4gooda(bufdesc_t *desc)
{
        int ret = valid4gooda(desc);

        fprintf(stderr,"Valid for Gooda: ");
        ret = - ret;
        if (ret >= NUM_GOODA_RESULTS)
                fprintf(stderr,"unknown reason\n");
        else
                fprintf(stderr,"%s\n", gooda_check_results[ret]);
#ifdef ANALYZE
	if(ret != 0)
		err(1,"perf.data file has invalid format for Gooda, upgrade perf and or Kernel and/or -R option was missing and is required\n");
#endif
}

static void usage(void)
{
	fprintf(stderr,"Usage: perf [-v] [-h] [-i] perf_data_file [-n] Val\n");
	fprintf(stderr," by default gooda will try to read perf data from ./perf.data\n");
	fprintf(stderr," use the -i option and the preferred file name to change this\n");
	fprintf(stderr," by default gooda will attempt to create annoted disassembly and source listings, and CFG displays\n");
	fprintf(stderr," for the hottest 20 functions. This limit can be changed by using the -n option followed by the number\n");
	fprintf(stderr," of functions that you desire having this more detailed data for.\n");
	fprintf(stderr," Increasing the number will slightly increase the runtime\n");
}

/*
 * XXX: READER ASSUMES SAME ENDIANESS BETWEEN WRITE OF perf.data and READER
 */
int
main(int argc, char **argv)
{
	int c,i,j,k,num_col,len;
	bufdesc_t desc;
        pointer_data * global_func_list;
	column_flag = 0;
	char def_file[] = "perf.data";
	char * file_name;

	file_name = def_file;
	

	while ((c= getopt(argc, argv, "i:h:n:v")) != -1) {
		switch(c) {
		case 'v':
			fprintf(stderr,"perf_reader v%s\n", PERF_READER_VERSION);
			exit(0);
		case 'h':
			usage();
			exit(0);
		case 'i':
			len = strlen(optarg);
			file_name = malloc(len+1);
			if(file_name == NULL)
				err(1,"cannot malloc buffer for input file name, len = %d",len);
			for(i=0; i<len; i++)file_name[i] = optarg[i];
			file_name[len] = '\0';
			break;
		case 'n':
			asm_cutoff = atoi(optarg);
			break;
		default:
			errx(1, "invalid argument key");
		}
	}
	memset(&desc, 0, sizeof(desc));

//	if (argc < 2)
//		errx(1, "need to pass a perf.data file");

	desc.fd = open(file_name, O_RDONLY);
	if (desc.fd == -1)
		err(1, "cannot open %s", argv[1]);
#ifdef ANALYZE
	init();
#endif

        if (detect_piped_file(&desc))
                read_pipe_header(&desc);
        else
                read_file_header(&desc);

	check4gooda(&desc);
	parse(&desc);

	fprintf(stderr,"finished reading input data file, commencing analysis\n");

#ifdef ANALYZE
#ifdef DBUGA
        dump_process_stack();
#endif

	create_dir();
	multiplex_correction();
#ifdef DBUGA
	column_flag = 1;
#endif
        reorder_process();
	if(global_func_count >= 1){
	        global_func_list = sort_global_func_list();
//		create a sorted list of sources and targets for each function
		if(lbr_ret != 0) 
			src_trg_func_list(global_func_list);
//		translate branch target/source addresses to function pointers and create a call count graph
		if(lbr_ret !=0)
			hotspot_call_graph(global_func_list);
//		printf out the function spreadsheet
        	hotspot_function( global_func_list);

		column_flag = 0;
//		loop through the hottest "asm_cuttoff" functions and create asm, source and cfg files
	        hot_list(global_func_list);

		num_col = num_events + global_event_order->num_branch + global_event_order->num_sub_branch +global_event_order->num_derived + 1;
        	fprintf(stderr," bad rva count = %d, with %d samples, out of global_rva = %d, with %d total samples in modules with functions and %d total samples\n",
			bad_rva, bad_sample_count, global_rva, total_function_sample_count, total_sample_count);
		fprintf(stderr," num_col = %d, num_events = %d, num_branch = %d, num_sub_branch = %d, num_derived = %d\n",
			num_col, num_events, global_event_order->num_branch, global_event_order->num_sub_branch, global_event_order->num_derived);
/*
		fprintf(stderr,"main: global_sample_count totals  ");
		for(i=0; i< num_col; i++)fprintf(stderr," %d,",global_sample_count[num_events*(num_cores+num_sockets) + i]);
		fprintf(stderr,"\n");
		fprintf(stderr,"main: global_sample_count per core , num_events = %d, num_cores = %d \n",num_events, num_cores);
		for(i=0; i< num_events; i++)
			{
			for(j=0; j<num_cores; j++)
				fprintf(stderr," %d,",global_sample_count[num_cores*i + j]);
			fprintf(stderr,"\n");
			}
*/
		fprintf(stderr,"normal termination\n");
		}
	else
		{
		fprintf(stderr,"No data in IP ranges defined by functions, exiting\n");
		}
#endif
	close(desc.fd);
	free(event_ids);
	return 0;
}
