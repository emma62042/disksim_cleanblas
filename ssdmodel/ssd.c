// DiskSim SSD support
// �2008 Microsoft Corporation. All Rights Reserved

#include "ssd.h"
#include "ssd_timing.h"
#include "ssd_clean.h"
#include "ssd_gang.h"
#include "ssd_init.h"
#include "modules/ssdmodel_ssd_param.h"
#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <stdlib.h>
//define-------------------------------------------------------
#define STRIPING 1	//the sequential logical page is replaced in every channel
#define LOCALITY 2	//the sequential logical page is replaced in a physical block
#define LRUSIZE 64
#define HASHSIZE 1000
#define CHANNEL_NUM 8
#define PLANE_NUM 8
#define TOTAL_NODE ((512*1024*80)/64)

//data struct-----------------------------------------------------------------------------------------------------------------
typedef struct _buffer_cache
{
	struct _lru_node *ptr_head; 				//lru list ,point to the group node head
	unsigned int total_buffer_page_num;			//current buffer page number in the cache
	unsigned int max_buffer_page_num;			//max buffer page count
	unsigned int w_hit_count;					//hit count for write (for statistics)
	unsigned int w_miss_count;					//miss count for write (for statistics)
	unsigned int r_hit_count;					//hit count for read (for statistics)
	unsigned int r_miss_count;					//miss count for read (for statistics)
	struct _lru_node *hash[HASHSIZE];			//hash table,quickly find the node ,hash by mod HASHSIZE
	struct _lru_node *ptr_current_mark_node;	//pointer the current mark node head,the point from the lru to mru 
	unsigned int current_mark_offset;			//the offset of current mark node ,using with ptr_current_mark_node together
}buffer_cache;
typedef struct _buffer_page
{
	unsigned int tmp;
	unsigned int exist2;  						//0 no exit;1 exit;2 have marked for special chip and plane
	unsigned char plane;						//when exist == 2,the value is meaningful
	unsigned char channel_num;					//the same as above
	unsigned int lpn;							//when page exist ,the value represent the logical page number
	struct _buffer_page *next;					//using only read intensive
	struct _buffer_page *prev;					//the same as above
	struct _lru_node *ptr_self_lru_node;		//pointer to self lru node
	unsigned char exist;
}buffer_page;
typedef struct  _lru_node
{
	unsigned int logical_node_num;				//logical_node_num == lpn / LRUSIZE
	unsigned int buffer_page_num;				//how many update page in this node
	unsigned char rw_intensive;					//what type is about this node
	buffer_page page[LRUSIZE];					//phy page in the node
	struct _lru_node *prev;						//link lru list
	struct _lru_node *next;
	struct _lru_node *h_prev;					//link hash list
	struct _lru_node *h_next;
	
}lru_node;
typedef struct _current_block_info //��structure���O���۸�cur blk�Y�쪺�O���@��LB(���]�O�Y��W-intensive��page)���qoffset�}�l�s�� cur_mark_cnt��pages
{
	lru_node *ptr_lru_node;							//point to current mark node,only using in write intensive
	unsigned int offset_in_node;					//the offset for pointer current mark node,only using in write intensive
	unsigned int current_mark_count;				//how many write intensive page in buffer be mark associate to current block
	unsigned int current_write_offset;				//how many page ready be written in current block
	struct _buffer_page *ptr_read_intensive_buffer_page;//only using in read intensive
	unsigned int read_intenisve_mark_count;
	unsigned int flush_r_count_in_current;			//how many read page has been flushed in current element 
	unsigned int flush_w_count_in_current;			//how many write page has been flushed in current plane
	double estimate_response_time;					//estimate every element response time	
}current_block_info;
struct access_count
{
	double read_count;								//read count for this trace 
	unsigned int total_page_size;	
	unsigned int rw_replacement;					//1:striping; 2:locality
	struct read_access_node *ptr_read_access_node;	//point the read access node
};
struct Statistics
{
	unsigned int kick_read_intensive_page_count;	//page is flashed to read intensive block 
	unsigned int kick_write_intensive_page_count;	//page is flashed to write intensive block
};
struct read_mark_plane
{
	int channel_num;
	int plane;
	int mark_count;
};
struct verify_value
{
	int handle_write_count_in_activity_elem;			//we sum the write count in the activities_elem function
									//the value should equal to kick_XXX_page_count
};
/*
 *we add the node to reduce the search time for finding a victim logical block to striping in all logical block
 *in the list,the max read access count will position in the head and min access will position in the tail
 *in addition,there are no request in the linked list with no any access count 
 */
 // sh: scattering list
struct read_access_node 
{
		unsigned int logical_number;		//corresponding to the logical block
		double read_count;		//this logical block access count
		struct read_access_node *next;		//double linked list 
		struct read_access_node *prev;
};
//ssd function prototype
static void ssd_request_complete(ioreq_event *curr);
static void ssd_media_access_request(ioreq_event *curr);

//function prototype------------------------------------------------------------------------------------------------------------
void init_buffer_cache(buffer_cache *ptr_buffer_cache);
void add_page_to_cache_buffer(unsigned int lpn,buffer_cache *ptr_buffer_cache);
void lsn2lpn(unsigned int input_lsa,unsigned  int input_scnt,unsigned int* req_lpn,unsigned int* req_cnt);
void add_a_node_to_buffer_cache(unsigned int logical_node_num,unsigned int offset_in_node,buffer_cache * ptr_buffer_cache);
void add_a_page_in_the_node(unsigned int logical_node_num,unsigned int offset_in_node,lru_node *ptr_lru_node,buffer_cache *ptr_buffer_cache );
int find_page_in_cache_buffer(unsigned int lpn,buffer_cache *ptr_buffer_cache);
void remove_a_page_in_the_node(unsigned int offset_in_node,lru_node *ptr_lru_node,buffer_cache *ptr_buffer_cache,unsigned int verify_channel,unsigned int verify_plane);
void add_and_remove_page_to_buffer_cache(ioreq_event *curr,buffer_cache *ptr_buffer_cache);
void mark_for_all_current_block(buffer_cache *ptr_buffer_cache);
void mark_for_specific_current_block(buffer_cache *ptr_buffer_cache,unsigned int channel_num,unsigned int plane);
void remove_mark_in_the_node(lru_node *ptr_lru_node,buffer_cache *ptr_buffer_cache);
void kick_page_from_buffer_cache(ioreq_event *curr,buffer_cache *ptr_buffer_cache);
void record_read_and_write_count(unsigned int lpn,unsigned int cnt,char w);
void remove_from_hash_and_lru(buffer_cache *ptr_buffer_cache,lru_node *ptr_lru_node);
void remve_read_intensive_page(unsigned int page_offset,lru_node *ptr_lru_node);
void mark_for_read_intensive_buffer(buffer_cache *ptr_buffer_cache);
void kick_read_intensive_page_from_buffer_cache(ioreq_event *curr,unsigned int channel_num,unsigned int plane,buffer_cache *ptr_buffer_cache);
void add_read_intensive_page_to_list(unsigned int page_offset,lru_node *ptr_lru_node);
void show_result(buffer_cache *ptr_buffer_cache);
void record_all_request_access_count(char *trace_file_name);
static void ssd_activate_elem(ssd_t *currdisk, int elem_num);
//speed up the search time
void add_node_to_read_access_list(unsigned int logical_number,double increase_score);
void increase_node_count(unsigned int logical_number,double increase_score);
int remove_and_get_a_victim_logical_block(void);
double remove_special_node(unsigned int logical_number);
//global varibale----------------------------------------------------------------------------------------------------------------
struct read_access_node *ptr_read_access_head_node = NULL;
struct access_count rw_count[TOTAL_NODE];
current_block_info current_block[CHANNEL_NUM][PLANE_NUM];
struct Statistics statistic;
buffer_cache my_buffer_cache;
struct read_mark_plane min_mark_plane[CHANNEL_NUM];
struct verify_value verify;
int req_check=0;


//-------------------------------------------------------------------------------------
#ifndef sprintf_s
#define sprintf_s3(x,y,z) sprintf(x,z)
#define sprintf_s4(x,y,z,w) sprintf(x,z,w)
#define sprintf_s5(x,y,z,w,s) sprintf(x,z,w,s)
#else
#define sprintf_s3(x,y,z) sprintf_s(x,z)
#define sprintf_s4(x,y,z,w) sprintf_s(x,z,w)
#define sprintf_s5(x,y,z,w,s) sprintf_s(x,z,w,s)
#endif

#ifndef _strdup
#define _strdup strdup
#endif
/*
 * when turn on this switch ,the buffer manager is not cooperation with ftl ,only kick the page of the block
 * the fix striping placement doesn't support this method
 * */
unsigned int block_level_lru_no_parallel = 0;
/*
 * 1.when a request arrived,we find the number of the sequetial page in the request and add to the scores.
 * if the more than the threshold,the logical block will prepare striping out 
 * 2.the method only accumulate the access count for every logical block when a request arrive
 * 3.In this method,our statistic (the history * 0.9) + (1 or -1) by the read or write
 * when the value more than a threshold ,we striping the logical block.
 *
 * */
unsigned int striping_threshold_method;
/*
 * if the variable set to 1,the program add the timing about the striping action
 * otherwise the program don't add the timing about the striping action
 * you can set 0 or non-zero when you need ...
 * */
unsigned int striping_timing_turn_on = 1;
/*
 * when we invoke the background striping machanism,the variable will not been zero
 * if we move N page to other channel ,the variable will been N
 * and  will reduce one since every page already finished move
 * */
double striping_threshold;
unsigned int striping_count = 0,striping_page = 0;
/*
 * a striping usually including max 7 page copy 
 * */
int background_striping = 0;
/*
 * statistics currently striping page count
 * */
double each_channel_striping_finish_time[CHANNEL_NUM];
double total_wait_striping_time;
unsigned int total_wait_striping_page_count;
/*
 * the previous variable are using by statisticing the striping resist the currently arrived page access
 * */
double w_multiple;
unsigned int init_locality;
/*
 *1:striping replacement
 *2:locality replacement
 * */
extern int GC_count_per_elem,GC_count_per_plane;
int total_gc_count,total_live_page_cp_count ;
extern unsigned int total_live_page_cp_count2;
extern page_level_mapping *lba_table;
unsigned int req_count;
unsigned int clear_statistic_data_req_count;
/*
 * the request will clare current statistic data 
 * */
unsigned int ack_req_count;
unsigned int total_access_page;//read page + write page count = req_count *average request size (including cache hit page)
unsigned int total_childCompTimeDif;//sh-- (last child's simtime -first child's simtime)

extern int table_size;
ssd_timing_params *params;
/*
 * only a pointer point the the struct of the SSDsim,convenient using by me
 * */
double method_para;

unsigned int write_request_count = 0,read_request_count = 0;
double write_total_serve_time = 0,read_total_serve_time = 0;
/*
 * fill block count is the number of a block is filled to the full
 * */
int fill_block_count = 0;
/*
 * total logical block count is the number of a physical block associate what many logical block count
 * */
int total_logical_block_count = 0;


char  trace_file_name[200];


struct ssd *getssd (int devno)
{
   struct ssd *s;
   ASSERT1((devno >= 0) && (devno < MAXDEVICES), "devno", devno);

   s = disksim->ssdinfo->ssds[devno];
   return (disksim->ssdinfo->ssds[devno]);
}

int ssd_set_depth (int devno, int inbusno, int depth, int slotno)
{
   ssd_t *currdisk;
   int cnt;

   currdisk = getssd (devno);
   assert(currdisk);
   cnt = currdisk->numinbuses;
   currdisk->numinbuses++;
   if ((cnt + 1) > MAXINBUSES) {
      fprintf(stderr, "Too many inbuses specified for ssd %d - %d\n", devno, (cnt+1));
      exit(1);
   }
   currdisk->inbuses[cnt] = inbusno;
   currdisk->depth[cnt] = depth;
   currdisk->slotno[cnt] = slotno;
   return(0);
}

int ssd_get_depth (int devno)
{
   ssd_t *currdisk;
   currdisk = getssd (devno);   
  
   return(currdisk->depth[0]);
}

int ssd_get_slotno (int devno)
{
   ssd_t *currdisk;
   currdisk = getssd (devno);
   return(currdisk->slotno[0]);
}

int ssd_get_inbus (int devno)
{
   ssd_t *currdisk;
   currdisk = getssd (devno);
   return(currdisk->inbuses[0]);
}

int ssd_get_maxoutstanding (int devno)
{
   ssd_t *currdisk;
   currdisk = getssd (devno);
   return(currdisk->maxqlen);
}

double ssd_get_blktranstime (ioreq_event *curr)
{
   ssd_t *currdisk;
   double tmptime;

   currdisk = getssd (curr->devno);
   tmptime = bus_get_transfer_time(ssd_get_busno(curr), 1, (curr->flags & READ));
   if (tmptime < currdisk->blktranstime) {
      tmptime = currdisk->blktranstime;
   }
   return(tmptime);
}

int ssd_get_busno (ioreq_event *curr)
{
   ssd_t *currdisk;
   intchar busno;
   int depth;

   currdisk = getssd (curr->devno);
   busno.value = curr->busno;
   depth = currdisk->depth[0];
   return(busno.byte[depth]);
}

static void ssd_assert_current_activity(ssd_t *currdisk, ioreq_event *curr)
{
    assert(currdisk->channel_activity != NULL &&
        currdisk->channel_activity->devno == curr->devno &&
        currdisk->channel_activity->blkno == curr->blkno &&
        currdisk->channel_activity->bcount == curr->bcount);
}

/*
 * ssd_send_event_up_path()
 *
 * Acquires the bus (if not already acquired), then uses bus_delay to
 * send the event up the path.
 *
 * If the bus is already owned by this device or can be acquired
 * immediately (interleaved bus), the event is sent immediately.
 * Otherwise, ssd_bus_ownership_grant will later send the event.
 */
static void ssd_send_event_up_path (ioreq_event *curr, double delay)
{
   ssd_t *currdisk;
   int busno;
   int slotno;

   // fprintf (outputfile, "ssd_send_event_up_path - devno %d, type %d, cause %d, blkno %d\n", curr->devno, curr->type, curr->cause, curr->blkno);

   currdisk = getssd (curr->devno);

   ssd_assert_current_activity(currdisk, curr);

   busno = ssd_get_busno(curr);
   slotno = currdisk->slotno[0];

   /* Put new request at head of buswait queue */
   curr->next = currdisk->buswait;
   currdisk->buswait = curr;

   curr->tempint1 = busno;
   curr->time = delay;
   if (currdisk->busowned == -1) {

      // fprintf (outputfile, "Must get ownership of the bus first\n");

      if (curr->next) {
         //fprintf(stderr,"Multiple bus requestors detected in ssd_send_event_up_path\n");
         /* This should be ok -- counting on the bus module to sequence 'em */
      }
      if (bus_ownership_get(busno, slotno, curr) == FALSE) {
         /* Remember when we started waiting (only place this is written) */
         currdisk->stat.requestedbus = simtime;
      } else {
         currdisk->busowned = busno;
         bus_delay(busno, DEVICE, curr->devno, delay, curr); /* Never for SCSI */
      }
   } else if (currdisk->busowned == busno) {

      //fprintf (outputfile, "Already own bus - so send it on up\n");

      bus_delay(busno, DEVICE, curr->devno, delay, curr);
   } else {
      fprintf(stderr, "Wrong bus owned for transfer desired\n");
      exit(1);
   }
}

/* The idea here is that only one request can "possess" the channel back to the
   controller at a time. All others are enqueued on queue of pending activities.
   "Completions" ... those operations that need only be signaled as done to the
   controller ... are given on this queue.  The "channel_activity" field indicates
   whether any operation currently possesses the channel.

   It is our hope that new requests cannot enter the system when the channel is
   possessed by another operation.  This would not model reality!!  However, this
   code (and that in ssd_request_arrive) will handle this case "properly" by enqueuing
   the incoming request.  */

static void ssd_check_channel_activity (ssd_t *currdisk)
{
   while (1) {
       ioreq_event *curr = currdisk->completion_queue;
       currdisk->channel_activity = curr;
       if (curr != NULL) {
           currdisk->completion_queue = curr->next;
           if (currdisk->neverdisconnect) {
               /* already connected */
               if (curr->flags & READ) {
                   /* transfer data up the line: curr->bcount, which is still set to */
                   /* original requested value, indicates how many blks to transfer. */
                   curr->type = DEVICE_DATA_TRANSFER_COMPLETE;
                   ssd_send_event_up_path(curr, (double) 0.0);
               } else {
                   ssd_request_complete (curr);
               }
           } else {
               /* reconnect to controller */
               curr->type = IO_INTERRUPT_ARRIVE;
               curr->cause = RECONNECT;
               ssd_send_event_up_path (curr, currdisk->bus_transaction_latency);
               currdisk->reconnect_reason = DEVICE_ACCESS_COMPLETE;
           }
       } else {
           curr = ioqueue_get_next_request(currdisk->queue);
           currdisk->channel_activity = curr;
           if (curr != NULL) {
               if (curr->flags & READ) {
                   if (!currdisk->neverdisconnect) {
                       ssd_media_access_request(ioreq_copy(curr));
                       curr->type = IO_INTERRUPT_ARRIVE;
                       curr->cause = DISCONNECT;
                       ssd_send_event_up_path (curr, currdisk->bus_transaction_latency);
                   } else {
                       ssd_media_access_request(curr);
                       continue;
                   }
               } else {
                   curr->cause = RECONNECT;
                   curr->type = IO_INTERRUPT_ARRIVE;
                   currdisk->reconnect_reason = IO_INTERRUPT_ARRIVE;
                   ssd_send_event_up_path (curr, currdisk->bus_transaction_latency);
               }
           }
       }
       break;
   }
}

/*
 * ssd_bus_ownership_grant
 * Calls bus_delay to handle the event that the disk has been granted the bus.  I believe
 * this is always initiated by a call to ssd_send_even_up_path.
 */
void ssd_bus_ownership_grant (int devno, ioreq_event *curr, int busno, double arbdelay)
{
   ssd_t *currdisk;
   ioreq_event *tmp;

   currdisk = getssd (devno);

   ssd_assert_current_activity(currdisk, curr);
   tmp = currdisk->buswait;
   while ((tmp != NULL) && (tmp != curr)) {
      tmp = tmp->next;
   }
   if (tmp == NULL) {
      fprintf(stderr, "Bus ownership granted to unknown ssd request - devno %d, busno %d\n", devno, busno);
      exit(1);
   }
   currdisk->busowned = busno;
   currdisk->stat.waitingforbus += arbdelay;
   //ASSERT (arbdelay == (simtime - currdisk->stat.requestedbus));
   currdisk->stat.numbuswaits++;
   bus_delay(busno, DEVICE, devno, tmp->time, tmp);
}

void ssd_bus_delay_complete (int devno, ioreq_event *curr, int sentbusno)
{
   ssd_t *currdisk;
   intchar slotno;
   intchar busno;
   int depth;

   currdisk = getssd (devno);
   ssd_assert_current_activity(currdisk, curr);

   // fprintf (outputfile, "Entered ssd_bus_delay_complete\n");

   // EPW: I think the buswait logic doesn't do anything, is confusing, and risks
   // overusing the "next" field, although an item shouldn't currently be a queue.
   if (curr == currdisk->buswait) {
      currdisk->buswait = curr->next;
   } else {
      ioreq_event *tmp = currdisk->buswait;
      while ((tmp->next != NULL) && (tmp->next != curr)) {
         tmp = tmp->next;
      }
      if (tmp->next != curr) {
          // fixed a warning here
          //fprintf(stderr, "Bus delay complete for unknown ssd request - devno %d, busno %d\n", devno, busno.value);
          fprintf(stderr, "Bus delay complete for unknown ssd request - devno %d, busno %d\n", devno, curr->busno);
         exit(1);
      }
      tmp->next = curr->next;
   }
   busno.value = curr->busno;
   slotno.value = curr->slotno;
   depth = currdisk->depth[0];
   slotno.byte[depth] = slotno.byte[depth] >> 4;
   curr->time = 0.0;
   if (depth == 0) {
      intr_request ((event *)curr);
   } else {
      bus_deliver_event(busno.byte[depth], slotno.byte[depth], curr);
   }
}


/*
 * send completion up the line
 */
static void ssd_request_complete(ioreq_event *curr)
{
   ssd_t *currdisk;
   ioreq_event *x;

   // fprintf (outputfile, "Entering ssd_request_complete: %12.6f\n", simtime);

   currdisk = getssd (curr->devno);
   ssd_assert_current_activity(currdisk, curr);

   if ((x = ioqueue_physical_access_done(currdisk->queue,curr)) == NULL) {
      fprintf(stderr, "ssd_request_complete:  ioreq_event not found by ioqueue_physical_access_done call\n");
      exit(1);
   }

   /* send completion interrupt */
   curr->type = IO_INTERRUPT_ARRIVE;
   curr->cause = COMPLETION;
   ssd_send_event_up_path(curr, currdisk->bus_transaction_latency);
}

static void ssd_bustransfer_complete (ioreq_event *curr)
{
   // fprintf (outputfile, "Entering ssd_bustransfer_complete for disk %d: %12.6f\n", curr->devno, simtime);

   if (curr->flags & READ) {
      ssd_request_complete (curr);
   } else {
      ssd_t *currdisk = getssd (curr->devno);
      ssd_assert_current_activity(currdisk, curr);
      if (currdisk->neverdisconnect == FALSE) {
          /* disconnect from bus */
          ioreq_event *tmp = ioreq_copy (curr);
          tmp->type = IO_INTERRUPT_ARRIVE;
          tmp->cause = DISCONNECT;
          ssd_send_event_up_path (tmp, currdisk->bus_transaction_latency);
          ssd_media_access_request (curr);
      } else {
          ssd_media_access_request (curr);
          ssd_check_channel_activity (currdisk);
      }
   }
}

/*
 * returns the logical page number within an element given a block number as
 * issued by the file system
 */
int ssd_logical_pageno(int blkno, ssd_t *s)
{
    int apn;
    int lpn;

    // absolute page number is the block number as written by the above layer
    apn = blkno/s->params.page_size;

    // find the logical page number within the ssd element. we maintain the
    // mapping between the logical page number and the actual physical page
    // number. an alternative is that we could maintain the mapping between
    // apn we calculated above and the physical page number. but the range
    // of apn is several times bigger and so we chose to go with the mapping
    // b/w lpn --> physical page number
   // lpn = ((apn - (apn % (s->params.element_stride_pages * s->params.nelements)))/
     //                 s->params.nelements) + (apn % s->params.element_stride_pages);

    return apn;
}

int ssd_already_present(ssd_req **reqs, int total, ioreq_event *req)
{
    int i;
    int found = 0;

    for (i = 0; i < total; i ++) {
        if ((req->blkno == reqs[i]->org_req->blkno) &&
            (req->flags == reqs[i]->org_req->flags)) {
            found = 1;
            break;
        }
    }

    return found;
}

double _ssd_invoke_element_cleaning(int elem_num, ssd_t *s)
{
	 
    double clean_cost = ssd_clean_element(s, elem_num);
    return clean_cost;
}

static int ssd_invoke_element_cleaning(int elem_num, ssd_t *s)
{
    double max_cost = 0;
    int cleaning_invoked = 0;
    ssd_element *elem = &s->elements[elem_num];

    // element must be free
    ASSERT(elem->media_busy == FALSE);

    max_cost = _ssd_invoke_element_cleaning(elem_num, s);

    // cleaning was invoked on this element. we can start
    // the next operation on this elem only after the cleaning
    // gets over.
    if (max_cost > 0) {
        ioreq_event *tmp;

        elem->media_busy = 1;
        cleaning_invoked = 1;

        // we use the 'blkno' field to store the element number
        tmp = (ioreq_event *)getfromextraq();
        tmp->devno = s->devno;
        tmp->time = simtime + max_cost;
        tmp->blkno = elem_num;
        tmp->ssd_elem_num = elem_num;
        tmp->type = SSD_CLEAN_ELEMENT;
        tmp->flags = SSD_CLEAN_ELEMENT;
        tmp->busno = -1;
        tmp->bcount = -1;
        stat_update (&s->stat.acctimestats, max_cost);
        addtointq ((event *)tmp);
	if(current_block[elem_num][0].estimate_response_time < max_cost + simtime)
	current_block[elem_num][0].estimate_response_time = max_cost + simtime;

        // stat
        elem->stat.tot_clean_time += max_cost;
    }

    return cleaning_invoked;
}

/*
 * we read the block page to another channel ,so the package would been set to busy
 * we used the clean event to represent the action
 * */
void set_time_for_this_elem_num(unsigned int elem_num,unsigned int seq_size)
{
	ssd_t *s =getssd(0);
	ioreq_event *tmp;
	ssd_element *elem;

	if(striping_timing_turn_on == 0)
	return ;

	elem = &s->elements[elem_num];
	elem->media_busy = TRUE;

  tmp = (ioreq_event *)getfromextraq();
  tmp->devno = s->devno;
  tmp->time = simtime + seq_size*ssd_data_transfer_cost(s,s->params.page_size) + s->params.page_read_latency;
  tmp->blkno = elem_num;
  tmp->ssd_elem_num = elem_num;
  tmp->type = SSD_CLEAN_ELEMENT;
  tmp->flags = SSD_CLEAN_ELEMENT;
  tmp->busno = -1;
  tmp->bcount = -1;
  //if(striping_timing_turn_on == 0)
	//{
		//tmp->time = simtime;
		//elem->media_busy = FALSE;
		//addtoextraq();
	//}
	
		each_channel_striping_finish_time[elem_num] = tmp->time; 
		addtointq ((event *)tmp);
	
}
/*
 * the function will striping lpn+1~lpn+seq_size-1 to the different channels
 sh--only used for scatter operation.
 * */
void assign_page_to_different_channel(unsigned int lpn,unsigned int seq_size)
{
 //printf("assign_page_to_different_channel(lpn=%d,seq_size=%d)\n",lpn,seq_size);
	int	elem_num = 0,plane_num = 0,i = 0;
	ssd_t *currdisk;
	ssd_element *elem;
	currdisk = getssd(0);
	elem_num = lba_table[lpn].elem_number;

	seq_size --;
	
	set_time_for_this_elem_num(elem_num,seq_size);   // sh--predict next idle time

	for(i = 1,seq_size;seq_size != 0;seq_size--,i++)
	{
		elem_num ++; //write to next elem
		if(elem_num == params->nelements)
			elem_num = 0;
		lpn++;
		elem = &currdisk->elements[elem_num];
		
	  // create a new sub-request for the element
    ioreq_event *tmp = (ioreq_event *)getfromextraq();
    tmp->devno = 0;
    tmp->busno = -1;
    tmp->flags = WRITE;
    tmp->blkno = lpn*currdisk->params.page_size;
    tmp->plane_num = find_max_free_page_in_plane(0,currdisk,elem_num);//	min_valid_page_in_plane(0,currdisk,elem_num);
    tmp->bcount = currdisk->params.page_size;
    tmp->tempptr2 = NULL;//when the tempptr2 == NULL,present this "write" is background scattering write.
		tmp->tempint2 = i;
		tmp->rw_intensive = 1;//read request

		elem->metadata.reqs_waiting ++;
		background_striping ++;
       // add the request to the corresponding element's queue
    ioqueue_add_new_request(elem->queue, (ioreq_event *)tmp);

	}
      
	for(i = 0;i < currdisk->params.nelements;i++)
	ssd_activate_elem(currdisk, i);
}

/*
 *
 * the function will find the logical sequential page is replacement in the same channel
 * */
void find_the_locality_page(int *striping_node,unsigned int *lpn,unsigned int *seq_size)
{
	int i = 0;
	*seq_size = 0;
	*lpn = (*striping_node)*LRUSIZE; // sh--LRUSIZE: LB page count
	//rw_count[*striping_node].rw_replacement = STRIPING;
	while(1)
	{
		if((*lpn + 1) % LRUSIZE == 0)
		{		
			*striping_node = -1;
			return ;
		}
		else if(lba_table[*lpn].elem_number != lba_table[*lpn + 1].elem_number)
			(*lpn) ++;
		else
			break;//find the sequential pages are replacement in the same channel
	}

	/*
	 * find length of the seqential page 
	 * */
	*seq_size = 1;
	for(i = 0;i < params->nelements -1 ;i++)
	{
		/*
		 * there probably more than the end page of the node to the new node ...,but there is no mind
		 * */
		if(lba_table[*lpn].elem_number == lba_table[*lpn + *seq_size].elem_number)
			(*seq_size) ++;
		else
			break;
	}
	/*
	 * when the node already striping ,we mark it to striping
	 * */
	if(((*lpn)%LRUSIZE) + *seq_size > LRUSIZE)
		rw_count[*striping_node].rw_replacement = STRIPING; // sh--��LB�Qscattered�������L��flag�� STRIPING

}

/*
 * the function will find the max read count for all node with rw_replacement
 * */
int find_the_read_dominate_node()
{
	int i = 0,max_node = -1;
//	int max_read_access = 3;//when access more than the variable ,we move is to other channels
	max_node = remove_and_get_a_victim_logical_block(); //max score node
	rw_count[max_node].read_count = 0;
#if 0
	for(i = 0;i <	TOTAL_NODE ;i++)
	{
		if(rw_count[i].read_count > max_read_access && rw_count[i].rw_replacement == LOCALITY){
			max_read_access = rw_count[i].read_count;
			max_node = i;
		}
	}
#endif
/*
 * when no any block want striping ,return -1
 * */	
	return max_node;
}
/*
 * return 0: don't invoke any striping mechanism
 * return 1: invoke striping mechanism
 *
 * the function will determinate whether the striping mechanism is invoked
 * */
int ssd_invoke_striping_data(void) //sh- background scattering
{
	int i = 0,lpn = 0,seq_size = 0;
	static int striping_node = -1; //!!! like global variable!!!!
	ssd_t *currdisk = getssd(0);
	/*
	 * when all channels are idle ,we invoke striping mechanism
	 * */
	if(background_striping != 0)
		return 0;
	for(i = 0;i < currdisk->params.nelements;i++)
	{
	    //sh -- try not to interfere foregroung requests
		if(currdisk->elements[i].metadata.reqs_waiting != 0 || currdisk->elements[i].media_busy == TRUE )
			return 0;
	}

	while(1)
	{
		/*
		 * find the striping node with page to be read frequently
		 * */
		if(striping_node == -1)
			striping_node = find_the_read_dominate_node();
		if(striping_node == -1)return 0;
		/*
		 * find the locality page in the node
		 * */
		find_the_locality_page(&striping_node,&lpn,&seq_size);
		if(striping_node != -1)break;
	}
	/*
	 * assign the page to every channel and set the time 
	 * */
	assert(seq_size != 1);
	striping_count ++;
	striping_page += seq_size;
	assign_page_to_different_channel(lpn,seq_size);

	
	return 1;
}
static void ssd_activate_elem(ssd_t *currdisk, int elem_num)
{
  //printf("!!!!!!ssd_activate_elem(\n");
    ioreq_event *req;
    ssd_req **read_reqs;
    ssd_req **write_reqs;
    int i,j;
    int read_total = 0;
    int write_total = 0;
    double schtime = 0;
    int max_reqs;
    int tot_reqs_issued;
	  double max_time_taken = 0;
    ssd_element *elem;

 		elem = &currdisk->elements[elem_num];

    // if the media is busy, we can't do anything, so return
    if (elem->media_busy == TRUE) {
        return;
    }
    ASSERT(ioqueue_get_reqoutstanding(elem->queue) == 0); /*SH--outstanding request: requests de-queued but not yet completed*/
	                                                      /*SH-- waiting request: request pending in queue*/

    // we can invoke cleaning in the background whether there
    // is request waiting or not  /*SH- ??? Doesn't bg means no pending request ? */
    
    if (currdisk->params.cleaning_in_background) {
        // if cleaning was invoked, wait until
        // it is over ...
        if (ssd_invoke_element_cleaning(elem_num, currdisk)) {
            return;
        }
				if(w_multiple == 999999)// this is needed! becuz scattering for P-strip-LB  is redundant.
				{
          printf("w_multiple == 999999\n");
					if(ssd_invoke_striping_data() == 1) //when entering this func., first thing is to check whether any LB-wait-to-be-scatter exit. 
					{
						return ;
					}
				}
				
    }

    ASSERT(elem->metadata.reqs_waiting == ioqueue_get_number_in_queue(elem->queue));

    if (elem->metadata.reqs_waiting > 0) {
					
        // invoke cleaning in foreground when there are requests waiting
        if (!currdisk->params.cleaning_in_background) {
            // if cleaning was invoked, wait until
            // it is over ...
            if (ssd_invoke_element_cleaning(elem_num, currdisk)) {
                return;
            }
        }
		/*clear the statistics flush count
		sh-- this two per-elem metadatas added by DJ is used to estimate shortest executed time of this elem
		Better place for this two metadata is in ssd_element structure.
		*/
		for(j = 0;j < currdisk->params.planes_per_pkg;j++)
		{
			current_block[elem_num][0].flush_w_count_in_current = 0;
			current_block[elem_num][0].flush_r_count_in_current = 0;
		}
        // how many reqs can we issue at once
        if (currdisk->params.copy_back == SSD_COPY_BACK_DISABLE) {
            max_reqs = 1;
        } else {
            if (currdisk->params.num_parunits == 1) {
                max_reqs = 1;
            } else {
                max_reqs = MAX_REQS_ELEM_QUEUE; //default 100
            }
        }

        // ideally, we should issue one req per plane, overlapping them all.
        // in order to simplify the overlapping strategy, let's issue
        // requests of the same type together.

        read_reqs = (ssd_req **) malloc(max_reqs * sizeof(ssd_req *));
        write_reqs = (ssd_req **) malloc(max_reqs * sizeof(ssd_req *));

        // collect the requests
        while ((req = ioqueue_get_next_request(elem->queue)) != NULL) {
            int found = 0;

            elem->metadata.reqs_waiting --;

            // see if we already have the same request in the list.
            // this usually doesn't happen -- but on synthetic traces
            // this weird case can occur.
            if (req->flags & READ) {
                found = ssd_already_present(read_reqs, read_total, req);
            } else {
								verify.handle_write_count_in_activity_elem ++;
                found = ssd_already_present(write_reqs, write_total, req);
            }

            if (!found) {
                // this is a valid request
                ssd_req *r = malloc(sizeof(ssd_req));
                r->blk = req->blkno;
                r->count = req->bcount;
                r->is_read = req->flags & READ;
                r->org_req = req;
                r->plane_num = -1; // we don't know to which plane this req will be directed at

                if (req->flags & READ) {
                    read_reqs[read_total] = r;
                    read_total ++;
                } else {
                    write_reqs[write_total] = r;
                    write_total ++;
                }

                // if we have more reqs than we can handle, quit
                if ((read_total >= max_reqs) ||
                    (write_total >= max_reqs)) {
                    break;
                }
            } else {
                // throw this request -- it doesn't make sense
                stat_update (&currdisk->stat.acctimestats, 0);
                req->time = simtime;
                req->ssd_elem_num = elem_num;
                req->type = DEVICE_ACCESS_COMPLETE;
                addtointq ((event *)req);
            }
        }


// so far, read & write�w�Q�������F�C  
		

        if (read_total > 0) {
            // first issue all the read requests (it doesn't matter what we
            // issue first). i chose read because reads are mostly synchronous.
            // find the time taken to serve these requests.
            ssd_compute_access_time(currdisk, elem_num, read_reqs, read_total);

            // add an event for each request completion
            for (i = 0; i < read_total; i ++) {
              elem->media_busy = TRUE;

              
              if (schtime < read_reqs[i]->schtime) {// find the maximum time taken by a request
                  schtime = read_reqs[i]->schtime;  //sh-- �̫�schtime�N�Olargest execution time of read req.
              }

              stat_update (&currdisk->stat.acctimestats, read_reqs[i]->acctime);
              read_reqs[i]->org_req->time = simtime + read_reqs[i]->schtime;
              read_reqs[i]->org_req->ssd_elem_num = elem_num;
              read_reqs[i]->org_req->type = DEVICE_ACCESS_COMPLETE;

              //printf("R: blk %d elem %d acctime %f simtime %f\n", read_reqs[i]->blk,
                //  elem_num, read_reqs[i]->acctime, read_reqs[i]->org_req->time);

              addtointq ((event *)read_reqs[i]->org_req);
              free(read_reqs[i]);
            }
        }

        free(read_reqs);
				if(current_block[elem_num][0].estimate_response_time < schtime + simtime)
					current_block[elem_num][0].estimate_response_time = schtime + simtime;
        max_time_taken = schtime;

        if (write_total > 0) {
            // next issue the write requests
            ssd_compute_access_time(currdisk, elem_num, write_reqs, write_total);

            // add an event for each request completion.
            // note that we can issue the writes only after all the reads above are
            // over. so, include the maximum read time when creating the event.
            for (i = 0; i < write_total; i ++) {
              elem->media_busy = TRUE;

              stat_update (&currdisk->stat.acctimestats, write_reqs[i]->acctime);
              write_reqs[i]->org_req->time = simtime + schtime + write_reqs[i]->schtime;
             
							/*
							 * the follow code is for striping write page .....
							 * when the tempptr2 == NULL,it represent the request is the striping write in the background
							 sh--there are two kinds of write: 1. user request, 2. scatter request(��tempptr2�Ӥ���)
							 * */
						 	if( write_reqs[i]->org_req->tempptr2 == NULL)
							{
								 assert( write_reqs[i]->org_req->tempint2 <= currdisk->params.nelements);

								 write_reqs[i]->org_req->time +=  write_reqs[i]->org_req->tempint2*ssd_data_transfer_cost(currdisk,currdisk->params.page_size);
								 //if( write_reqs[i]->org_req->tempint2 == 1)
										write_reqs[i]->org_req->time += params->page_read_latency;

								 /*
								 if(striping_timing_turn_on == 0)//when we skip the access time about the striping action
								 {
									 write_reqs[i]->org_req->time = simtime;
									//	 elem->media_busy = FALSE;
								 }
								 */
								 //set the finish time for striping action
								 each_channel_striping_finish_time[elem_num] =  write_reqs[i]->org_req->time;
							}

              if (max_time_taken < (schtime+write_reqs[i]->schtime)) {
                  max_time_taken = (schtime+write_reqs[i]->schtime);
              }

              write_reqs[i]->org_req->ssd_elem_num = elem_num;
              write_reqs[i]->org_req->type = DEVICE_ACCESS_COMPLETE;
              //printf("W: blk %d elem %d acctime %f simtime %f\n", write_reqs[i]->blk,
                //  elem_num, write_reqs[i]->acctime, write_reqs[i]->org_req->time);
              addtointq ((event *)write_reqs[i]->org_req);
              free(write_reqs[i]);
            }
        }

        free(write_reqs);
	if(current_block[elem_num][0].estimate_response_time < max_time_taken + simtime)
	current_block[elem_num][0].estimate_response_time = max_time_taken + simtime;
        // statistics
        tot_reqs_issued = read_total + write_total;
        ASSERT(tot_reqs_issued > 0);
        currdisk->elements[elem_num].stat.tot_reqs_issued += tot_reqs_issued;
        currdisk->elements[elem_num].stat.tot_time_taken += max_time_taken;
    }
}
int min_response_elem(ssd_t *currdisk)
{
	double estimate_time[currdisk->params.nelements];
	int i = 0,j = 0,min_elem,w_count,min_valid_elem = -1,min_valid_page,valid_pages,total_mark_page = 0;
	double min_response_value = 999999999;
	for(i = 0;i < currdisk->params.nelements;i++)
	{
		w_count = 0;
		total_mark_page = 0;
		for(j = 0;j < currdisk->params.planes_per_pkg;j++)
		{
			w_count += current_block[i][j].flush_w_count_in_current;
			total_mark_page += current_block[i][j].current_mark_count + current_block[i][j].read_intenisve_mark_count;
		}
		if(current_block[i][0].estimate_response_time > simtime)
		estimate_time[i] = current_block[i][0].estimate_response_time - simtime;
		else 
		estimate_time[i] = 0;
		estimate_time[i] += (double)current_block[i][0].flush_r_count_in_current*(double)ssd_data_transfer_cost(currdisk,currdisk->params.page_size)\
							+ (double)w_count*currdisk->params.page_write_latency;
		if(total_mark_page == 0)
			estimate_time[i] = -1;
		
	}	
//min_elem = 0;
//min_response_value = estimate_time[0];
	for(i = 0;i < currdisk->params.nelements;i++)
	{
		if(min_response_value > estimate_time[i]&&estimate_time[i] != -1)
		{
			min_elem = i;
			min_response_value = estimate_time[i];
		}
	}
	for(i = 0;i < currdisk->params.nelements; i++)
	{
		if(estimate_time[i] == 0&&estimate_time[i] != -1)//if many estimate are 0,put the req to the min valid pages elements
		{
			valid_pages = 0;
			for(j = 0;j < currdisk->params.planes_per_pkg;j++)
			{
				valid_pages += currdisk->elements[i].metadata.plane_meta[j].valid_pages;
			}
			if(min_valid_elem == -1 ||valid_pages < min_valid_page)
			{
				min_valid_page = valid_pages;
				min_valid_elem = i;
			}
		}
	}
	if(min_valid_elem == -1)
		return min_elem;
	else
	return min_valid_elem;
}
/*
 * min_response_elem2 is more accurate than min_response_elem in finding the min 
 * but there are more complicate than min_response_elem 
 * */

int min_response_elem2(ssd_t *currdisk,unsigned int *die_num)
{
	/*
	 * statistic the response for all die
	 * */
	double estimate_time[currdisk->params.nelements][currdisk->params.nelements/SSD_PLANES_PER_PARUNIT(currdisk)];
	int i = 0,j = 0,k = 0,z = 0,min_elem,min_die;
	/*
	 * statistic all write page in a die
	 * */
	int w_count[SSD_PLANES_PER_PARUNIT(currdisk)];
	int min_valid_elem = -1,min_valid_die = -1,min_valid_page,valid_pages,total_mark_page = 0;
	/*
	 * in order to the the min reponse ,we set the value to very large
	 * */
	double min_response_value = 999999999;

	/*init the array*/
	for(i = 0;i < SSD_PLANES_PER_PARUNIT(currdisk);i++)
	{
		w_count[i] = 0;
	}
	/*
	 * find the min response die and package
	 * */
	/*
	 * for every package
	 * */
	for(i = 0;i < currdisk->params.nelements;i++)
	{
		/*
		 * for every die
		 * */
		for(k = 0;k < SSD_PARUNITS_PER_ELEM(currdisk); k++)
		{
			w_count[k] = 0;
			total_mark_page = 0;
			/*
			 * for every plane
			 * */
			for(j = 0;j < SSD_PLANES_PER_PARUNIT(currdisk);j++)
			{
				w_count[k] += current_block[i][j + k*SSD_PLANES_PER_PARUNIT(currdisk)].flush_w_count_in_current;
				total_mark_page += current_block[i][j + k*SSD_PLANES_PER_PARUNIT(currdisk)].current_mark_count \
													 + current_block[i][j + k*SSD_PLANES_PER_PARUNIT(currdisk)].read_intenisve_mark_count;
				
				assert(!(current_block[i][j + k*SSD_PLANES_PER_PARUNIT(currdisk)].read_intenisve_mark_count != 0 &&\
					 	current_block[i][j + k*SSD_PLANES_PER_PARUNIT(currdisk)].ptr_read_intensive_buffer_page == NULL));
			}
		
			if(current_block[i][0].estimate_response_time > simtime)
				estimate_time[i][k] = current_block[i][0].estimate_response_time - simtime;
			else 
				estimate_time[i][k] = 0;
			/*
			 * for read page :
			 * we only compute the data transfer time and the one time read time,because the transfer time is more than the read time
			 * for write page:
			 * we consider the write latency and the transfer time
			 * */
			estimate_time[i][k] += (double)current_block[i][0].flush_r_count_in_current*(double)ssd_data_transfer_cost(currdisk,currdisk->params.page_size)\
							+ (double)w_count[k]*(currdisk->params.page_write_latency);
			
			for(z = 0;z < SSD_PLANES_PER_ELEM(currdisk)/SSD_PLANES_PER_PARUNIT(currdisk);z++)
			{
				/*
				 * the code is stistics the bus waiting time
				 * */
				estimate_time[i][z] += (double)ssd_data_transfer_cost(currdisk,currdisk->params.page_size)*(double)w_count[k];
				/*
				 * add the read latency one time
				 * */	
			}
			
			if(total_mark_page == 0)
					estimate_time[i][k] = -1;
		}/*end for every die*/
	}	/*end for every package*/

	/*find the min response time package and die*/
	for(i = 0;i < currdisk->params.nelements;i++)
	{
		for(k = 0;k < SSD_PLANES_PER_ELEM(currdisk)/SSD_PLANES_PER_PARUNIT(currdisk); k++)
		{
			for(j = 0;j < SSD_PLANES_PER_PARUNIT(currdisk);j++)
			{
				if(min_response_value > estimate_time[i][k]&&estimate_time[i][k] != -1&&\
						(!(current_block[i][j + k*SSD_PLANES_PER_PARUNIT(currdisk)].ptr_read_intensive_buffer_page == NULL&& \
						 current_block[i][j + k*SSD_PLANES_PER_PARUNIT(currdisk)].current_mark_count == 0))&&\
					 	currdisk->elements[i].metadata.plane_meta[j + k*SSD_PLANES_PER_PARUNIT(currdisk)].valid_pages < (5120 - 20)*63)
				{
					min_elem = i;
					min_die = k;
					min_response_value = estimate_time[i][k];
				}
			}
		}
	}
	/*
	 * if mamy package and die are dile in the current time,we find the plane in the die and package with min valid page
	 * */
	
	for(i = 0;i < currdisk->params.nelements; i++)
	{
		for(k = 0;k < SSD_PLANES_PER_ELEM(currdisk)/SSD_PLANES_PER_PARUNIT(currdisk);k++)
		{
			if(estimate_time[i][k] == 0 && !(current_block[i][j + k*SSD_PLANES_PER_PARUNIT(currdisk)].ptr_read_intensive_buffer_page == NULL&& \
						 current_block[i][j + k*SSD_PLANES_PER_PARUNIT(currdisk)].current_mark_count == 0))
			{		
				valid_pages = 0;
				for(j = 0;j < SSD_PLANES_PER_PARUNIT(currdisk);j++)
				{
					valid_pages += currdisk->elements[i].metadata.plane_meta[j + k*SSD_PLANES_PER_PARUNIT(currdisk)].valid_pages;
				}/*end for every plane in the die*/
				
				if(min_valid_elem == -1 ||valid_pages < min_valid_page)
				{
					/*find the die with min valid page */
					min_valid_page = valid_pages;
					min_valid_elem = i;
					min_valid_die = k;
				}
			}
		}/*end for every die in the package*/
	}/*end for every package in the ssd*/
	if(min_valid_elem == -1)
	{
		*die_num = min_die;
		return min_elem;
	}
	else
	{
		*die_num = min_valid_die;
		return min_valid_elem;
	}
}

int min_valid_page_in_plane(int die_num,ssd_t *currdisk,int elem_num)
{
	int plane_num = 0; //die_num *SSD_PLANES_PER_PARUNIT(currdisk);
	int min,min_plane;
	for(plane_num;plane_num<8/*die_num *SSD_PLANES_PER_PARUNIT(currdisk)+SSD_PLANES_PER_PARUNIT(currdisk)*/;plane_num++)
	{
		if(plane_num == 0/*die_num*SSD_PLANES_PER_PARUNIT(currdisk)*/)
		{
			min = currdisk->elements[elem_num].metadata.plane_meta[plane_num].valid_pages +\
							current_block[elem_num][plane_num].flush_w_count_in_current;
			min_plane = plane_num;
		}
		else if(min>currdisk->elements[elem_num].metadata.plane_meta[plane_num].valid_pages + \
							current_block[elem_num][plane_num].flush_w_count_in_current)
		{
			min = currdisk->elements[elem_num].metadata.plane_meta[plane_num].valid_pages + 
							current_block[elem_num][plane_num].flush_w_count_in_current;
			min_plane = plane_num;
		}
	}
	current_block[elem_num][min_plane].flush_w_count_in_current ++;
	return min_plane;
}
int max_free_page_in_plane(int die_num,ssd_t *currdisk,int elem_num);
int min_valid_page_in_plane2(int die_num,ssd_t *currdisk,int elem_num)
{
	int plane_num = 0; //die_num *SSD_PLANES_PER_PARUNIT(currdisk);
	unsigned  int min = 999999999,min_plane = -1;
	plane_metadata *pm;
	for(plane_num;plane_num < params->planes_per_pkg;plane_num++)
	{
		pm = &currdisk->elements[elem_num].metadata.plane_meta[plane_num];
	
		if((min > pm->valid_pages + current_block[elem_num][plane_num].flush_w_count_in_current)&&\
				!(current_block[elem_num][plane_num].read_intenisve_mark_count == 0 &&current_block[elem_num][plane_num].current_mark_count == 0))
		{
			min = pm->free_blocks*SSD_DATA_PAGES_PER_BLOCK(currdisk) - current_block[elem_num][plane_num].flush_w_count_in_current;
			min_plane = plane_num;
		}
	}
	if(min_plane == -1)
	{
		min_plane = max_free_page_in_plane(0,currdisk,elem_num);
	}
	return min_plane;
}


int max_free_page_in_plane(int die_num,ssd_t *currdisk,int elem_num)
{
	int plane_num = 0; //die_num *SSD_PLANES_PER_PARUNIT(currdisk);
	unsigned  int min = 0,min_plane = -1;
	plane_metadata *pm;
	for(plane_num;plane_num < params->planes_per_pkg;plane_num++)
	{
		pm = &currdisk->elements[elem_num].metadata.plane_meta[plane_num];
	/*	if(plane_num == 0)
		{
			min = pm->free_blocks*SSD_DATA_PAGES_PER_BLOCK(currdisk)	+ current_block[elem_num][plane_num].flush_w_count_in_current;
			min_plane = plane_num;
		}
		elsei*/ 
		if((min < pm->free_blocks*SSD_DATA_PAGES_PER_BLOCK(currdisk) - current_block[elem_num][plane_num].flush_w_count_in_current)&&\
				!(current_block[elem_num][plane_num].read_intenisve_mark_count == 0 &&current_block[elem_num][plane_num].current_mark_count == 0))
		{
			min = pm->free_blocks*SSD_DATA_PAGES_PER_BLOCK(currdisk) - current_block[elem_num][plane_num].flush_w_count_in_current;
			min_plane = plane_num;
		}
	}
	return min_plane;

}
int max_free_page_in_plane2(int die_num,ssd_t *currdisk,int elem_num)
{
	int plane_num = 0; //die_num *SSD_PLANES_PER_PARUNIT(currdisk);
	unsigned  int min = 0,min_plane = -1;
	plane_metadata *pm;
	int i =0;
	/*
	 * travel the all plane in the special die
	 * */
		for(plane_num = die_num * SSD_PLANES_PER_PARUNIT(currdisk);plane_num < (die_num + 1)*SSD_PLANES_PER_PARUNIT(currdisk);plane_num++)	
		{
			pm = &currdisk->elements[elem_num].metadata.plane_meta[plane_num];
	
			if((min < pm->free_blocks*SSD_DATA_PAGES_PER_BLOCK(currdisk) - current_block[elem_num][plane_num].flush_w_count_in_current)&&\
					(currdisk->elements[elem_num].metadata.plane_meta[plane_num].valid_pages < (5120 - 20)*63)&&\
			!(current_block[elem_num][plane_num].read_intenisve_mark_count == 0 && current_block[elem_num][plane_num].ptr_read_intensive_buffer_page == NULL))
			{
				min = pm->free_blocks*SSD_DATA_PAGES_PER_BLOCK(currdisk) - current_block[elem_num][plane_num].flush_w_count_in_current;
				min_plane = plane_num;
			}
		}

	/*
	 * travel again and relax the restrictions
	 * */
	if(min_plane == -1)
	{
		for(plane_num = 0;plane_num < SSD_PLANES_PER_ELEM(currdisk);plane_num++)
		{
			pm = &currdisk->elements[elem_num].metadata.plane_meta[plane_num];

			if((min < pm->free_blocks*SSD_DATA_PAGES_PER_BLOCK(currdisk))&&\
				!(current_block[elem_num][plane_num].read_intenisve_mark_count == 0 &&current_block[elem_num][plane_num].current_mark_count == 0))
			{
				min = pm->free_blocks*SSD_DATA_PAGES_PER_BLOCK(currdisk);// - current_block[elem_num][plane_num].flush_w_count_in_current;
				min_plane = plane_num;
			}
		}
	}

	/*
	 * travel again and relax the restrictions
	 * */
	if(min_plane == -1)
	{
		for(elem_num = 0;elem_num < currdisk->params.nelements;elem_num ++){
		for(plane_num = 0;plane_num < SSD_PLANES_PER_ELEM(currdisk);plane_num++)
		{
			if(!(current_block[elem_num][plane_num].read_intenisve_mark_count == 0 && current_block[elem_num][plane_num].current_mark_count == 0))
			{
				min_plane = plane_num;
			}
		}
		}
	}
	
	if(min_plane <= 8)
	{
	//	printf("%d\n",min_plane);
	
	assert(min_plane < 8);
	}
	assert(min_plane != -1);

	return min_plane;

}
/*
 * the finction is used in striping page ,we find a plane with max free page
 * */
int find_max_free_page_in_plane(int die_num,ssd_t *currdisk,int elem_num)
{
	int plane_num = 0; //die_num *SSD_PLANES_PER_PARUNIT(currdisk);
	unsigned  int min = 0,min_plane = -1;
	plane_metadata *pm;
	for(plane_num = 0;plane_num < params->planes_per_pkg;plane_num ++)
	{
		pm = &currdisk->elements[elem_num].metadata.plane_meta[plane_num];
	
		if(min < pm->free_blocks*SSD_DATA_PAGES_PER_BLOCK(currdisk))
		{
			min = pm->free_blocks*SSD_DATA_PAGES_PER_BLOCK(currdisk);
			min_plane = plane_num;
		}
	}
	return min_plane;

}

void show_some_info(void)
{
	int i,j;
	for(i = 0;i<8;i++)
	{
		for(j = 0;j<8;j++)
		{
			printf("ytc94u %d ",current_block[i][j].read_intenisve_mark_count);
		}
		printf("ytc94u\n");
	}

}
unsigned int	pre_write_request_count = 0, pre_read_request_count = 0;
unsigned int	pre_write_total_serve_time = 0, pre_read_total_serve_time = 0;
unsigned int pre_striping_count = 0,pre_striping_page = 0;
unsigned int pre_total_live_page_cp_count = 0;
static void statistic_the_data_in_every_stage()
{
			//show_some_info();
			printf("ytc94u %u total_live_page_cp_count2 = %u W resp time = %lf R resp time = %lf resp time = %lf \
				 	striping count = %u striping page = %u\n total_childcompTimeDiff = %f",ack_req_count,total_live_page_cp_count2 - pre_total_live_page_cp_count,\
				(double)(write_total_serve_time - pre_write_total_serve_time) /	(double)(write_request_count - pre_write_request_count) ,\
				(double)(read_total_serve_time - pre_read_total_serve_time)/(double)(read_request_count - pre_read_request_count),\
				
				((double)(write_total_serve_time - pre_write_total_serve_time)+(double)(read_total_serve_time - pre_read_total_serve_time))/\
				((double)(write_request_count - pre_write_request_count)+(double)(read_request_count - pre_read_request_count)),
				
				(striping_count - pre_striping_count),(striping_page - pre_striping_page),total_childCompTimeDif);

			pre_total_live_page_cp_count = total_live_page_cp_count2 ;
			
			pre_write_request_count = write_request_count;
			pre_read_request_count = read_request_count;
			pre_write_total_serve_time = write_total_serve_time;
			pre_read_total_serve_time = read_total_serve_time ;

			pre_striping_count = striping_count;
			pre_striping_page = striping_page;

			if(clear_statistic_data_req_count == ack_req_count && clear_statistic_data_req_count != 0)
			{
				write_request_count = read_request_count = 0;
				write_total_serve_time = read_total_serve_time = 0;
				total_live_page_cp_count2 = total_gc_count = 0;
		
				pre_total_live_page_cp_count = total_live_page_cp_count2 ;
			
			
				pre_write_request_count = write_request_count = 0;
				pre_read_request_count = read_request_count = 0;
				pre_write_total_serve_time = write_total_serve_time = 0;
				pre_read_total_serve_time = read_total_serve_time = 0;

				pre_striping_count = striping_count = 0;
				pre_striping_page = striping_page = 0;


				GC_count_per_elem = GC_count_per_plane = GC_count_per_plane = GC_count_per_elem = 0;
				total_wait_striping_time = total_wait_striping_page_count = 0;
			}

}


void statistics_the_wait_time_by_striping(int elem_num)
{
		
	/*statistic the total page with being resisted by stripking action */
	if(each_channel_striping_finish_time[elem_num] > simtime)
	{
	     
		total_wait_striping_time += each_channel_striping_finish_time[elem_num] - simtime;
		total_wait_striping_page_count ++;
	}

}
static void ssd_media_access_request_element (ioreq_event *curr)
{
 //printf("inininininin\n");
  req_check++;
  printf("req_check=%d\n",req_check);
  ssd_t *currdisk = getssd(curr->devno);
  int blkno = curr->blkno;
 //printf("blkno=%d\n",blkno);
  int count = curr->bcount; //sh--req block count( must be multiple of 8)
  static int sta_elem_num = 0,sta_die_num = 0,sta_plane_num = 0,first_run_this = 0;
  int i = 0,elem_num,plane_num;
  unsigned int lpn;
	int hit = 0;
	 //when first request arrive,we initialized the cache 
  if(first_run_this == 0)
  {
    init_buffer_cache(&my_buffer_cache);
		params = &currdisk->params;
   	first_run_this = 1;
  }
 	//curr->arrive_time = simtime; 
   /* **** CAREFUL ... HIJACKING tempint2 and tempptr2 fields here **** */
   req_count ++;
   total_access_page += curr->bcount/currdisk->params.page_size;
#if 0
	 if(req_count %/* 3142853 */100000 == 0)
   {
		 statistic_the_data_in_every_stage();
   }
#endif

	 /*
		* the request type is write data...
		* */
   if(!(curr->flags&READ))
   {
			record_read_and_write_count(ssd_logical_pageno(curr->blkno,currdisk),curr->bcount/currdisk->params.page_size,'w');

			add_and_remove_page_to_buffer_cache(curr,&my_buffer_cache);
			for(i=0;i<currdisk->params.nelements;i++)
				ssd_activate_elem(currdisk, i);
     //printf("if(!(curr->flags&READ))\n");
			return ;
   }







   
	 /*
	   * the follow code is used for read request...
          */

   assert(curr->flags&READ);
  //printf("assert(curr->flags&READ);\n");
   
   curr->tempint2 = count;//sh- record "parent's total fs-block count"

   while (count != 0) {

       // find the element (package) to direct the request
       // int elem_num = currdisk->timing_t->choose_element(currdisk->timing_t, blkno);// sh-- static method by orignal disksim
  	 sta_elem_num ++;
  	
  	 if(curr->flags&READ)/*sh-- if read, lookup table directly*/
  	 {	 
  		elem_num = lba_table[ssd_logical_pageno(blkno,currdisk)].elem_number;
      int ppn = lba_table[ssd_logical_pageno(blkno,currdisk)].ppn;
     //printf("elem_num=%d,ppn=%d\n", elem_num, ppn);
  		lpn = ssd_logical_pageno(blkno,currdisk);
  	 }
  	 else
  		  assert(0); //sh-- teminate program and report line number if this line is executed.


  	   ssd_element *elem = &currdisk->elements[elem_num];

  	 /*create a new sub-request for the element*/
       ioreq_event *tmp = (ioreq_event *)getfromextraq();
       tmp->devno = curr->devno;
       tmp->busno = curr->busno;
  	   tmp->flags = curr->flags;
       tmp->blkno = blkno;
       tmp->plane_num = plane_num;//sh--useless on read !
       tmp->bcount = ssd_choose_aligned_count(currdisk->params.page_size, blkno, count);
       ASSERT(tmp->bcount == currdisk->params.page_size);
       tmp->tempptr2 = curr;// pointer to the parent

  	 
       blkno += tmp->bcount;
       count -= tmp->bcount;
  	 // read hit in cache
       if(find_page_in_cache_buffer(lpn,&my_buffer_cache))
       {
  			 hit = 1;
  			 ssd_complete_parent(tmp,currdisk);
  			 addtoextraq(tmp);
  			 continue;
  	   }
  	   current_block[elem_num][0].flush_r_count_in_current++;//sh-- for estimation of shotest execution time per elem.
  		 
  	   statistics_the_wait_time_by_striping(elem_num);
  			//the elem increase a wait page
       elem->metadata.reqs_waiting ++;
         // add the request to the corresponding element's queue
       ioqueue_add_new_request(elem->queue, (ioreq_event *)tmp);
	 }
	
	 if(hit == 0)
		 record_read_and_write_count(ssd_logical_pageno(curr->blkno,currdisk),curr->bcount/currdisk->params.page_size,'r');
	
	 for(i=0;i<currdisk->params.nelements;i++)
		 ssd_activate_elem(currdisk, i);

}

static void ssd_media_access_request (ioreq_event *curr)
{
    ssd_t *currdisk = getssd(curr->devno);

    switch(currdisk->params.alloc_pool_logic) {
        case SSD_ALLOC_POOL_PLANE:
        case SSD_ALLOC_POOL_CHIP:
            ssd_media_access_request_element(curr);
        break;

        case SSD_ALLOC_POOL_GANG:
#if SYNC_GANG
            ssd_media_access_request_gang_sync(curr);
#else
            ssd_media_access_request_gang(curr);
#endif
        break;

        default:
            printf("Unknown alloc pool logic %d\n", currdisk->params.alloc_pool_logic);
            ASSERT(0);
    }
}

static void ssd_reconnect_done (ioreq_event *curr)
{
   ssd_t *currdisk;

   // fprintf (outputfile, "Entering ssd_reconnect_done for disk %d: %12.6f\n", curr->devno, simtime);

   currdisk = getssd (curr->devno);
   ssd_assert_current_activity(currdisk, curr);

   if (curr->flags & READ) {
      if (currdisk->neverdisconnect) {
         /* Just holding on to bus; data transfer will be initiated when */
         /* media access is complete.                                    */
         addtoextraq((event *) curr);
         ssd_check_channel_activity (currdisk);
      } else {
         /* data transfer: curr->bcount, which is still set to original */
         /* requested value, indicates how many blks to transfer.       */
         curr->type = DEVICE_DATA_TRANSFER_COMPLETE;
         ssd_send_event_up_path(curr, (double) 0.0);
      }

   } else {
      if (currdisk->reconnect_reason == DEVICE_ACCESS_COMPLETE) {
         ssd_request_complete (curr);

      } else {
         /* data transfer: curr->bcount, which is still set to original */
         /* requested value, indicates how many blks to transfer.       */
         curr->type = DEVICE_DATA_TRANSFER_COMPLETE;
         ssd_send_event_up_path(curr, (double) 0.0);
      }
   }
}

static void ssd_request_arrive (ioreq_event *curr)
{
   ssd_t *currdisk;

   // fprintf (outputfile, "Entering ssd_request_arrive: %12.6f\n", simtime);
   // fprintf (outputfile, "ssd = %d, blkno = %d, bcount = %d, read = %d\n",curr->devno, curr->blkno, curr->bcount, (READ & curr->flags));

   currdisk = getssd(curr->devno);

   /* verify that request is valid. */
   if ((curr->blkno < 0) || (curr->bcount <= 0) ||
       ((curr->blkno + curr->bcount) > currdisk->numblocks)) {
      fprintf(stderr, "Invalid set of blocks requested from ssd - blkno %d, bcount %d, numblocks %d\n", curr->blkno, curr->bcount, currdisk->numblocks);
      exit(1);
   }

   /* create a new request, set it up for initial interrupt */
   ioqueue_add_new_request(currdisk->queue, curr);
   if (currdisk->channel_activity == NULL) {

      curr = ioqueue_get_next_request(currdisk->queue);
      currdisk->busowned = ssd_get_busno(curr);
      currdisk->channel_activity = curr;
      currdisk->reconnect_reason = IO_INTERRUPT_ARRIVE;

      if (curr->flags & READ) {
          if (!currdisk->neverdisconnect) {
              ssd_media_access_request (ioreq_copy(curr));
              curr->cause = DISCONNECT;
              curr->type = IO_INTERRUPT_ARRIVE;
              ssd_send_event_up_path(curr, currdisk->bus_transaction_latency);
          } else {
              ssd_media_access_request (curr);
              ssd_check_channel_activity(currdisk);
          }
      } else {
         curr->cause = READY_TO_TRANSFER;
         curr->type = IO_INTERRUPT_ARRIVE;
         ssd_send_event_up_path(curr, currdisk->bus_transaction_latency);
      }
   }
}

/*
 * cleaning in an element is over.
 */
static void ssd_clean_element_complete(ioreq_event *curr)
{
   ssd_t *currdisk;
   int elem_num;

   currdisk = getssd (curr->devno);
   elem_num = curr->ssd_elem_num;
   ASSERT(currdisk->elements[elem_num].media_busy == TRUE);

   // release this event
   addtoextraq((event *) curr);

   // activate the gang to serve the next set of requests
   currdisk->elements[elem_num].media_busy = 0;
   ssd_activate_elem(currdisk, elem_num);
}
void total_serve_time(ioreq_event *parent)
{
	if(parent->flags&READ)
	{
		read_request_count++;
		read_total_serve_time += simtime - parent->arrive_time;
	}
	else
	{
		write_request_count++;
		write_total_serve_time += simtime - parent->arrive_time;
	}
}
/*
 *
 * */
void striping_request_finished(void)
{
	background_striping--;
	assert(background_striping >= 0);
}
void ssd_complete_parent(ioreq_event *curr, ssd_t *currdisk)
{
	 
    ioreq_event *parent;

    /* **** CAREFUL ... HIJACKING tempint2 and tempptr2 fields here **** */
    /*
		 * if the temmptr2 == NULL,represent the request is used to striping write
		 * */
	if(curr->tempptr2 == NULL){
		striping_request_finished();
		return ;
	}
	parent = curr->tempptr2;

	if(parent->tempint3 == 0)
    parent->tempint3=simtime;//sh-- first child completed time
	
    parent->tempint2 -= curr->bcount;

    if (parent->tempint2 == 0) 
		{
			ack_req_count ++;
			total_childCompTimeDif += simtime - parent->tempint3; //sh
			if(ack_req_count % 500000 == 0 ||clear_statistic_data_req_count  == ack_req_count)
			{
			 	statistic_the_data_in_every_stage();
			}
      ioreq_event *prev;
			total_serve_time(parent);
      //assert(parent != currdisk->channel_activity);
      prev = currdisk->completion_queue;
      if (prev == NULL) {
         currdisk->completion_queue = parent;
         parent->next = prev;
      } else {
         while (prev->next != NULL)
            prev = prev->next;
            parent->next = prev->next;
            prev->next = parent;
      }
      if (currdisk->channel_activity == NULL) {
         ssd_check_channel_activity (currdisk);
      }
    }
}

static void ssd_access_complete_element(ioreq_event *curr)
{
   ssd_t *currdisk;
   int elem_num;
   ssd_element  *elem;
   ioreq_event *x;

   currdisk = getssd (curr->devno);
   elem_num = curr->ssd_elem_num; // currdisk->timing_t->choose_element(currdisk->timing_t, curr->blkno);
   ASSERT(elem_num == curr->ssd_elem_num);
   elem = &currdisk->elements[elem_num];

   if ((x = ioqueue_physical_access_done(elem->queue,curr)) == NULL) {
      fprintf(stderr, "ssd_access_complete:  ioreq_event not found by ioqueue_physical_access_done call\n");
      exit(1);
   }

   // all the reqs are over
   if (ioqueue_get_reqoutstanding(elem->queue) == 0) {
    elem->media_busy = FALSE;
   }

   ssd_complete_parent(curr, currdisk);
   addtoextraq((event *) curr);
   ssd_activate_elem(currdisk, elem_num);
}

static void ssd_access_complete(ioreq_event *curr)
{
    ssd_t *currdisk = getssd (curr->devno);;

    switch(currdisk->params.alloc_pool_logic) {
        case SSD_ALLOC_POOL_PLANE:
        case SSD_ALLOC_POOL_CHIP:
            ssd_access_complete_element(curr);
        break;

        case SSD_ALLOC_POOL_GANG:
#if SYNC_GANG
            ssd_access_complete_gang_sync(curr);
#else
            ssd_access_complete_gang(curr);
#endif
        break;

        default:
            printf("Unknown alloc pool logic %d\n", currdisk->params.alloc_pool_logic);
            ASSERT(0);
    }
}

/* intermediate disconnect done */
static void ssd_disconnect_done (ioreq_event *curr)
{
   ssd_t *currdisk;

   currdisk = getssd (curr->devno);
   ssd_assert_current_activity(currdisk, curr);

   // fprintf (outputfile, "Entering ssd_disconnect for disk %d: %12.6f\n", currdisk->devno, simtime);

   addtoextraq((event *) curr);

   if (currdisk->busowned != -1) {
      bus_ownership_release(currdisk->busowned);
      currdisk->busowned = -1;
   }
   ssd_check_channel_activity (currdisk);
}

/* completion disconnect done */
static void ssd_completion_done (ioreq_event *curr)
{
   ssd_t *currdisk = getssd (curr->devno);
   ssd_assert_current_activity(currdisk, curr);

   // fprintf (outputfile, "Entering ssd_completion for disk %d: %12.6f\n", currdisk->devno, simtime);

   addtoextraq((event *) curr);

   if (currdisk->busowned != -1) {
      bus_ownership_release(currdisk->busowned);
      currdisk->busowned = -1;
   }

   ssd_check_channel_activity (currdisk);
}

static void ssd_interrupt_complete (ioreq_event *curr)
{
   // fprintf (outputfile, "Entered ssd_interrupt_complete - cause %d\n", curr->cause);

   switch (curr->cause) {

      case RECONNECT:
         ssd_reconnect_done(curr);
     break;

      case DISCONNECT:
     ssd_disconnect_done(curr);
     break;

      case COMPLETION:
     ssd_completion_done(curr);
     break;

      default:
         ddbg_assert2(0, "bad event type");
   }
}


void ssd_event_arrive (ioreq_event *curr)
{
   ssd_t *currdisk;

   // fprintf (outputfile, "Entered ssd_event_arrive: time %f (simtime %f)\n", curr->time, simtime);
   // fprintf (outputfile, " - devno %d, blkno %d, type %d, cause %d, read = %d\n", curr->devno, curr->blkno, curr->type, curr->cause, curr->flags & READ);

   currdisk = getssd (curr->devno);

   switch (curr->type) {

      case IO_ACCESS_ARRIVE:
         curr->time = simtime + currdisk->overhead;
         curr->type = DEVICE_OVERHEAD_COMPLETE;
         addtointq((event *) curr);
         break;

      case DEVICE_OVERHEAD_COMPLETE:
         ssd_request_arrive(curr);
         break;

      case DEVICE_ACCESS_COMPLETE:
         ssd_access_complete (curr);
         break;

      case DEVICE_DATA_TRANSFER_COMPLETE:
         ssd_bustransfer_complete(curr);
         break;

      case IO_INTERRUPT_COMPLETE:
         ssd_interrupt_complete(curr);
         break;

      case IO_QLEN_MAXCHECK:
         /* Used only at initialization time to set up queue stuff */
         curr->tempint1 = -1;
         curr->tempint2 = ssd_get_maxoutstanding(curr->devno);
         curr->bcount = 0;
         break;

      case SSD_CLEAN_GANG:
          ssd_clean_gang_complete(curr);
          break;

      case SSD_CLEAN_ELEMENT:
          ssd_clean_element_complete(curr);
          break;

        default:
         fprintf(stderr, "Unrecognized event type at ssd_event_arrive\n");
         exit(1);
   }

   // fprintf (outputfile, "Exiting ssd_event_arrive\n");
}


int ssd_get_number_of_blocks (int devno)
{
   ssd_t *currdisk = getssd (devno);
   return (currdisk->numblocks);
}


int ssd_get_numcyls (int devno)
{
   ssd_t *currdisk = getssd (devno);
   return (currdisk->numblocks);
}


void ssd_get_mapping (int maptype, int devno, int blkno, int *cylptr, int *surfaceptr, int *blkptr)
{
   ssd_t *currdisk = getssd (devno);

   if ((blkno < 0) || (blkno >= currdisk->numblocks)) {
      fprintf(stderr, "Invalid blkno at ssd_get_mapping: %d\n", blkno);
      exit(1);
   }

   if (cylptr) {
      *cylptr = blkno;
   }
   if (surfaceptr) {
      *surfaceptr = 0;
   }
   if (blkptr) {
      *blkptr = 0;
   }
}


int ssd_get_avg_sectpercyl (int devno)
{
   return (1);
}


int ssd_get_distance (int devno, ioreq_event *req, int exact, int direction)
{
   /* just return an arbitrary constant, since acctime is constant */
   return 1;
}


// returning 0 to remove warning
double  ssd_get_servtime (int devno, ioreq_event *req, int checkcache, double maxtime)
{
   fprintf(stderr, "device_get_seektime not supported for ssd devno %d\n",  devno);
   assert(0);
   return 0;
}


// returning 0 to remove warning
double  ssd_get_acctime (int devno, ioreq_event *req, double maxtime)
{
   fprintf(stderr, "device_get_seektime not supported for ssd devno %d\n",  devno);
   assert(0);
   return 0;
}


int ssd_get_numdisks (void)
{
   return(numssds);
}


void ssd_cleanstats (void)
{
   int i, j;

   for (i=0; i<MAXDEVICES; i++) {
      ssd_t *currdisk = getssd (i);
      if (currdisk) {
          ioqueue_cleanstats(currdisk->queue);
          for (j=0; j<currdisk->params.nelements; j++)
              ioqueue_cleanstats(currdisk->elements[j].queue);
      }
   }
}

void ssd_setcallbacks ()
{
   ioqueue_setcallbacks();
}

int ssd_add(struct ssd *d) {
  int c;

  if(!disksim->ssdinfo) ssd_initialize_diskinfo();

  for(c = 0; c < disksim->ssdinfo->ssds_len; c++) {
    if(!disksim->ssdinfo->ssds[c]) {
      disksim->ssdinfo->ssds[c] = d;
      numssds++;
      return c;
    }
  }

  /* note that numdisks must be equal to diskinfo->disks_len */
  disksim->ssdinfo->ssds =
    realloc(disksim->ssdinfo->ssds,
        2 * c * sizeof(struct ssd *));

  bzero(disksim->ssdinfo->ssds + numssds,
    numssds);

  disksim->ssdinfo->ssds[c] = d;
  numssds++;
  disksim->ssdinfo->ssds_len *= 2;
  return c;
}


struct ssd *ssdmodel_ssd_loadparams(struct lp_block *b, int *num)
{
  /* temp vars for parameters */
  int n;
  struct ssd *result;

  if(!disksim->ssdinfo) ssd_initialize_diskinfo();

  result = malloc(sizeof(struct ssd));
  if(!result) return 0;
  bzero(result, sizeof(struct ssd));

  n = ssd_add(result);

  result->hdr = ssd_hdr_initializer;
  if(b->name)
    result->hdr.device_name = _strdup(b->name);

  lp_loadparams(result, b, &ssdmodel_ssd_mod);

  device_add((struct device_header *)result, n);
  if (num != NULL)
	  *num = n;
  return result;
}


struct ssd *ssd_copy(struct ssd *orig) {
  int i;
  struct ssd *result = malloc(sizeof(struct ssd));
  bzero(result, sizeof(struct ssd));
  memcpy(result, orig, sizeof(struct ssd));
  result->queue = ioqueue_copy(orig->queue);
  for (i=0;i<orig->params.nelements;i++)
      result->elements[i].queue = ioqueue_copy(orig->elements[i].queue);
  return result;
}

void ssd_set_syncset (int setstart, int setend)
{
}


static void ssd_acctime_printstats (int *set, int setsize, char *prefix)
{
   int i;
   statgen * statset[MAXDEVICES];

   if (device_printacctimestats) {
      for (i=0; i<setsize; i++) {
         ssd_t *currdisk = getssd (set[i]);
         statset[i] = &currdisk->stat.acctimestats;
      }
      stat_print_set(statset, setsize, prefix);
   }
}


static void ssd_other_printstats (int *set, int setsize, char *prefix)
{
   int i;
   int numbuswaits = 0;
   double waitingforbus = 0.0;

   for (i=0; i<setsize; i++) {
      ssd_t *currdisk = getssd (set[i]);
      numbuswaits += currdisk->stat.numbuswaits;
      waitingforbus += currdisk->stat.waitingforbus;
   }

   fprintf(outputfile, "%sTotal bus wait time: %f\n", prefix, waitingforbus);
   fprintf(outputfile, "%sNumber of bus waits: %d\n", prefix, numbuswaits);
}

void ssd_print_block_lifetime_distribution(int elem_num, ssd_t *s, int ssdno, double avg_lifetime, char *sourcestr)
{
    const int bucket_size = 20;
    int no_buckets = (100/bucket_size + 1);
    int i;
    int *hist;
    int dead_blocks = 0;
    int n;
    double sum;
    double sum_sqr;
    double mean;
    double variance;
    ssd_element_metadata *metadata = &(s->elements[elem_num].metadata);

    // allocate the buckets
    hist = (int *) malloc(no_buckets * sizeof(int));
    memset(hist, 0, no_buckets * sizeof(int));

    // to calc the variance
    n = s->params.blocks_per_element;
    sum = 0;
    sum_sqr = 0;

    for (i = 0; i < s->params.blocks_per_element; i ++) {
        int bucket;
        int rem_lifetime = metadata->block_usage[i].rem_lifetime;
        double perc = (rem_lifetime * 100.0) / avg_lifetime;

        // find out how many blocks have completely been erased.
        if (metadata->block_usage[i].rem_lifetime == 0) {
            dead_blocks ++;
        }

        if (perc >= 100) {
            // this can happen if a particular block was not
            // cleaned at all and so its remaining life time
            // is greater than the average life time. put these
            // blocks in the last bucket.
            bucket = no_buckets - 1;
        } else {
            bucket = (int) perc / bucket_size;
        }

        hist[bucket] ++;

        // calculate the variance
        sum = sum + rem_lifetime;
        sum_sqr = sum_sqr + (rem_lifetime*rem_lifetime);
    }


    fprintf(outputfile, "%s #%d elem #%d   ", sourcestr, ssdno, elem_num);
    fprintf(outputfile, "Block Lifetime Distribution\n");

    // print the bucket size
    fprintf(outputfile, "%s #%d elem #%d   ", sourcestr, ssdno, elem_num);
    for (i = bucket_size; i <= 100; i += bucket_size) {
        fprintf(outputfile, "< %d\t", i);
    }
    fprintf(outputfile, ">= 100\t\n");

    // print the histogram bar lengths
    fprintf(outputfile, "%s #%d elem #%d   ", sourcestr, ssdno, elem_num);
    for (i = bucket_size; i <= 100; i += bucket_size) {
        fprintf(outputfile, "%d\t", hist[i/bucket_size - 1]);
    }
    fprintf(outputfile, "%d\t\n", hist[no_buckets - 1]);

    mean = sum/n;
    variance = (sum_sqr - sum*mean)/(n - 1);
    fprintf(outputfile, "%s #%d elem #%d   Average of life time:\t%f\n",
        sourcestr, ssdno, elem_num, mean);
    fprintf(outputfile, "%s #%d elem #%d   Variance of life time:\t%f\n",
        sourcestr, ssdno, elem_num, variance);
    fprintf(outputfile, "%s #%d elem #%d   Total dead blocks:\t%d\n",
        sourcestr, ssdno, elem_num, dead_blocks);
}

//prints the cleaning algo statistics
void ssd_printcleanstats(int *set, int setsize, char *sourcestr)
{
    int i;
    int tot_ssd = 0;
    int elts_count = 0;
    double iops = 0;

    fprintf(outputfile, "\n\nSSD CLEANING STATISTICS\n");
    fprintf(outputfile, "---------------------------------------------\n\n");
    for (i = 0; i < setsize; i ++) {
        int j;
        int tot_elts = 0;
        ssd_t *s = getssd(set[i]);

        if (s->params.write_policy == DISKSIM_SSD_WRITE_POLICY_OSR) {

            elts_count += s->params.nelements;

            for (j = 0; j < s->params.nelements; j ++) {
                int plane_num;
                double avg_lifetime;
                double elem_iops = 0;
                double elem_clean_iops = 0;

                ssd_element_stat *stat = &(s->elements[j].stat);

                avg_lifetime = ssd_compute_avg_lifetime(-1, j, s);

                fprintf(outputfile, "%s #%d elem #%d   Total reqs issued:\t%d\n",
                    sourcestr, set[i], j, s->elements[j].stat.tot_reqs_issued);
                fprintf(outputfile, "%s #%d elem #%d   Total time taken:\t%f\n",
                    sourcestr, set[i], j, s->elements[j].stat.tot_time_taken);
                if (s->elements[j].stat.tot_time_taken > 0) {
                    elem_iops = ((s->elements[j].stat.tot_reqs_issued*1000.0)/s->elements[j].stat.tot_time_taken);
                    fprintf(outputfile, "%s #%d elem #%d   IOPS:\t%f\n",
                        sourcestr, set[i], j, elem_iops);
                }

                fprintf(outputfile, "%s #%d elem #%d   Total cleaning reqs issued:\t%d\n",
                    sourcestr, set[i], j, s->elements[j].stat.num_clean);
                fprintf(outputfile, "%s #%d elem #%d   Total cleaning time taken:\t%f\n",
                    sourcestr, set[i], j, s->elements[j].stat.tot_clean_time);
                fprintf(outputfile, "%s #%d elem #%d   Total migrations:\t%d\n",
                    sourcestr, set[i], j, s->elements[j].metadata.tot_migrations);
                fprintf(outputfile, "%s #%d elem #%d   Total pages migrated:\t%d\n",
                    sourcestr, set[i], j, s->elements[j].metadata.tot_pgs_migrated);
                fprintf(outputfile, "%s #%d elem #%d   Total migrations cost:\t%f\n",
                    sourcestr, set[i], j, s->elements[j].metadata.mig_cost);


                if (s->elements[j].stat.tot_clean_time > 0) {
                    elem_clean_iops = ((s->elements[j].stat.num_clean*1000.0)/s->elements[j].stat.tot_clean_time);
                    fprintf(outputfile, "%s #%d elem #%d   clean IOPS:\t%f\n",
                        sourcestr, set[i], j, elem_clean_iops);
                }

                fprintf(outputfile, "%s #%d elem #%d   Overall IOPS:\t%f\n",
                    sourcestr, set[i], j, ((s->elements[j].stat.num_clean+s->elements[j].stat.tot_reqs_issued)*1000.0)/(s->elements[j].stat.tot_clean_time+s->elements[j].stat.tot_time_taken));

                iops += elem_iops;

                fprintf(outputfile, "%s #%d elem #%d   Number of free blocks:\t%d\n",
                    sourcestr, set[i], j, s->elements[j].metadata.tot_free_blocks);
                fprintf(outputfile, "%s #%d elem #%d   Number of cleans:\t%d\n",
                    sourcestr, set[i], j, stat->num_clean);
                fprintf(outputfile, "%s #%d elem #%d   Pages moved:\t%d\n",
                    sourcestr, set[i], j, stat->pages_moved);
                fprintf(outputfile, "%s #%d elem #%d   Total xfer time:\t%f\n",
                    sourcestr, set[i], j, stat->tot_xfer_cost);
                if (stat->tot_xfer_cost > 0) {
                    fprintf(outputfile, "%s #%d elem #%d   Xfer time per page:\t%f\n",
                        sourcestr, set[i], j, stat->tot_xfer_cost/(1.0*stat->pages_moved));
                } else {
                    fprintf(outputfile, "%s #%d elem #%d   Xfer time per page:\t0\n",
                        sourcestr, set[i], j);
                }
                fprintf(outputfile, "%s #%d elem #%d   Average lifetime:\t%f\n",
                    sourcestr, set[i], j, avg_lifetime);
                fprintf(outputfile, "%s #%d elem #%d   Plane Level Statistics\n",
                    sourcestr, set[i], j);
                fprintf(outputfile, "%s #%d elem #%d   ", sourcestr, set[i], j);
                for (plane_num = 0; plane_num < s->params.planes_per_pkg; plane_num ++) {
                    fprintf(outputfile, "%d:(%d)  ",
                        plane_num, s->elements[j].metadata.plane_meta[plane_num].num_cleans);
                }
                fprintf(outputfile, "\n");


                ssd_print_block_lifetime_distribution(j, s, set[i], avg_lifetime, sourcestr);
                fprintf(outputfile, "\n");

                tot_elts += stat->pages_moved;
            }

            //fprintf(outputfile, "%s SSD %d average # of pages moved per element %d\n",
            //  sourcestr, set[i], tot_elts / s->params.nelements);

            tot_ssd += tot_elts;
            fprintf(outputfile, "\n");
        }
    }

    if (elts_count > 0) {
        fprintf(outputfile, "%s   Total SSD IOPS:\t%f\n",
            sourcestr, iops);
        fprintf(outputfile, "%s   Average SSD element IOPS:\t%f\n",
            sourcestr, iops/elts_count);
    }

    //fprintf(outputfile, "%s SSD average # of pages moved per ssd %d\n\n",
    //  sourcestr, tot_ssd / setsize);
}

void ssd_printsetstats (int *set, int setsize, char *sourcestr)
{
   int i;
   struct ioq * queueset[MAXDEVICES*SSD_MAX_ELEMENTS];
   int queuecnt = 0;
   int reqcnt = 0;
   char prefix[80];

   //using more secure functions
   sprintf_s4(prefix, 80, "%sssd ", sourcestr);
   for (i=0; i<setsize; i++) {
      ssd_t *currdisk = getssd (set[i]);
      struct ioq *q = currdisk->queue;
      queueset[queuecnt] = q;
      queuecnt++;
      reqcnt += ioqueue_get_number_of_requests(q);
   }
   if (reqcnt == 0) {
      fprintf (outputfile, "\nNo ssd requests for members of this set\n\n");
      return;
   }
   ioqueue_printstats(queueset, queuecnt, prefix);

   ssd_acctime_printstats(set, setsize, prefix);
   ssd_other_printstats(set, setsize, prefix);
}


void ssd_printstats (void)
{
   struct ioq * queueset[MAXDEVICES*SSD_MAX_ELEMENTS];
   int set[MAXDEVICES];
   int i,j;
   int reqcnt = 0;
   char prefix[80];
   int diskcnt;
   int queuecnt;
    fprintf(outputfile, "\nSSD STATISTICS\n");
   fprintf(outputfile, "---------------------\n\n");
   show_result(&my_buffer_cache);
   sprintf_s3(prefix, 80, "ssd ");

   diskcnt = 0;
   queuecnt = 0;
   for (i=0; i<MAXDEVICES; i++) {
      ssd_t *currdisk = getssd (i);
      if (currdisk) {
         struct ioq *q = currdisk->queue;
         queueset[queuecnt] = q;
         queuecnt++;
         reqcnt += ioqueue_get_number_of_requests(q);
         diskcnt++;
      }
   }
   assert (diskcnt == numssds);

   if (reqcnt == 0) {
      fprintf(outputfile, "No ssd requests encountered\n");
      return;
   }

   ioqueue_printstats(queueset, queuecnt, prefix);

   diskcnt = 0;
   for (i=0; i<MAXDEVICES; i++) {
      ssd_t *currdisk = getssd (i);
      if (currdisk) {
         set[diskcnt] = i;
         diskcnt++;
      }
   }
   assert (diskcnt == numssds);

   ssd_acctime_printstats(set, numssds, prefix);
   ssd_other_printstats(set, numssds, prefix);

   ssd_printcleanstats(set, numssds, prefix);

   fprintf (outputfile, "\n\n");

   for (i=0; i<numssds; i++) {
      ssd_t *currdisk = getssd (set[i]);
      if (currdisk->printstats == FALSE) {
          continue;
      }
      reqcnt = 0;
      {
          struct ioq *q = currdisk->queue;
          reqcnt += ioqueue_get_number_of_requests(q);
      }
      if (reqcnt == 0) {
          fprintf(outputfile, "No requests for ssd #%d\n\n\n", set[i]);
          continue;
      }
      fprintf(outputfile, "ssd #%d:\n\n", set[i]);
      sprintf_s4(prefix, 80, "ssd #%d ", set[i]);
      {
          struct ioq *q;
          q = currdisk->queue;
          ioqueue_printstats(&q, 1, prefix);
      }
      for (j=0;j<currdisk->params.nelements;j++) {
          char pprefix[100];
          struct ioq *q;
          sprintf_s5(pprefix, 100, "%s elem #%d ", prefix, j);
          q = currdisk->elements[j].queue;
          ioqueue_printstats(&q, 1, pprefix);
      }
      ssd_acctime_printstats(&set[i], 1, prefix);
      ssd_other_printstats(&set[i], 1, prefix);
      fprintf (outputfile, "\n\n");
   }
}

// returning 0 to remove warning
double ssd_get_seektime (int devno,
                ioreq_event *req,
                int checkcache,
                double maxtime)
{
  fprintf(stderr, "device_get_seektime not supported for ssd devno %d\n",  devno);
  assert(0);
  return 0;
}

/* default ssd dev header */
struct device_header ssd_hdr_initializer = {
  DEVICETYPE_SSD,
  sizeof(struct ssd),
  "unnamed ssd",
  (void *)ssd_copy,
  ssd_set_depth,
  ssd_get_depth,
  ssd_get_inbus,
  ssd_get_busno,
  ssd_get_slotno,
  ssd_get_number_of_blocks,
  ssd_get_maxoutstanding,
  ssd_get_numcyls,
  ssd_get_blktranstime,
  ssd_get_avg_sectpercyl,
  ssd_get_mapping,
  ssd_event_arrive,
  ssd_get_distance,
  ssd_get_servtime,
  ssd_get_seektime,
  ssd_get_acctime,
  ssd_bus_delay_complete,
  ssd_bus_ownership_grant
};
// i add code from there -------------------------------------------------------------
//------------------------------------------------------------------------------------
//------------------------------------------------------------------------------------
//------------------------------------------------------------------------------------
//------------------------------------------------------------------------------------
//------------------------------------------------------------------------------------
//------------------------------------------------------------------------------------
#if 0
void record_all_request_access_count(char *trace_file_name)
{
	FILE *trace_pf;
	double time;
	unsigned int tmp,lsn,rw;
	int sector_size;
	ssd_t *currdisk;	
	currdisk = getssd (0);
	trace_pf = fopen(trace_file_name,"r");
	assert(trace_pf);
	while(1)
	{
		fscanf(trace_pf,"%lf %u %u %u %u\n",&time,&tmp,&lsn,&sector_size,&rw);
		if(feof(trace_pf))break;
		while(1)
		{
			if(rw == 0)
			{
					rw_count[(lsn/currdisk->params.page_size)/LRUSIZE].write_count ++;
			}
			else if(rw == 1)
			{
						rw_count[(lsn/currdisk->params.page_size)/LRUSIZE].read_count ++;
			}
			else
				assert(0);
			lsn += currdisk->params.page_size;
			sector_size -= currdisk->params.page_size;
			if(sector_size <= 0)break;

		}
	}
}
#endif
void init_buffer_cache(buffer_cache *ptr_buffer_cache)
{
	FILE *pf2,*pf;
	unsigned int yyy,sector,len,rw,lpn,cnt;
	double xxx;
	int max_buffer_page_num;
	int i = 0;
	pf = fopen("para_file","r");
	fscanf(pf,"%d %lf %s",&max_buffer_page_num,&w_multiple,trace_file_name);
 //printf("max_buffer_page_num=%d\n", max_buffer_page_num);
	fclose(pf);
	pf = fopen("para_file2","r");
	fscanf(pf,"%u",&init_locality);
	fclose(pf);
//	record_all_request_access_count(trace_file_name);
	ptr_buffer_cache->ptr_head = NULL;
	ptr_buffer_cache->total_buffer_page_num = 0;
	ptr_buffer_cache->max_buffer_page_num = max_buffer_page_num;
	ptr_buffer_cache->w_hit_count = ptr_buffer_cache->w_miss_count = 0;
	ptr_buffer_cache->r_hit_count = ptr_buffer_cache->r_miss_count = 0;
	memset(ptr_buffer_cache->hash,0,sizeof(lru_node *)*HASHSIZE);
	ptr_buffer_cache->ptr_current_mark_node = NULL;
	ptr_buffer_cache->current_mark_offset = 0;

	/*
	 * init the access table
	 * */

	if(init_locality == LOCALITY)
	{
		for(i = 0;i < TOTAL_NODE;i++)
		{
			rw_count[i].rw_replacement = LOCALITY;
		}
	}
	else
	{
		for(i = 0;i < TOTAL_NODE;i++)
		{
			rw_count[i].rw_replacement = STRIPING;
		}
	}

}
void record_read_and_write_count(unsigned int lpn,unsigned int cnt,char w)
{
   //printf("lpn=%d\n", lpn);
		unsigned int lpn_start_node = 0,lpn_end_node = 0,end_lpn = lpn + cnt -1;
		unsigned int page_size = 0;
		double increase_score = 0;
		lpn_start_node = lpn/LRUSIZE;
		lpn_end_node = (lpn + cnt - 1)/LRUSIZE;

						
		if(w == 'w' || w == 'W')
		{									
			for(;lpn_start_node <= lpn_end_node;lpn_start_node ++)
			{

					/*for the mathod 3,we don't reset the score to zero*/
					if(rw_count[lpn_start_node].read_count != 0)
					{
						remove_special_node(lpn_start_node);
					}
					rw_count[lpn_start_node].total_page_size =	rw_count[lpn_start_node].read_count = 0;
				}
				rw_count[lpn_start_node].rw_replacement = LOCALITY;

		}
		else
		{
			for(;lpn_start_node <= lpn_end_node;lpn_start_node ++)
			{
				if(rw_count[lpn_start_node].rw_replacement == STRIPING)
					continue;

				/*
				 * striping threshold method 1
				 * */
				if(striping_threshold_method == 1)
				{
					page_size = ( lpn_start_node + 1 )*LRUSIZE - lpn;
					lpn = ( lpn_start_node + 1 )*LRUSIZE;
					if(lpn_start_node == lpn_end_node)
					{
						page_size = page_size - ((lpn_end_node + 1)*LRUSIZE - end_lpn -1);
					}
				
					
					page_size = page_size/8;

//if(rw_count[lpn_start_node].total_page_size + page_size > 255)return ;
					if(rw_count[lpn_start_node].read_count != 0)
					increase_score =  (double)1 + ((double)(rw_count[lpn_start_node].total_page_size + page_size )/\
							((double)rw_count[lpn_start_node].read_count + 1 ))*method_para \
													 - ((double)rw_count[lpn_start_node].total_page_size/(double)rw_count[lpn_start_node].read_count)*method_para;
					else
						increase_score = 1 + (double)page_size*method_para;
					rw_count[lpn_start_node].total_page_size	= rw_count[lpn_start_node].total_page_size + page_size;
				}
				/*
				 * striping threshold method 2
				 * */
				if(striping_threshold_method == 2)
				{
					increase_score = 1;
				}
	
				/*
				 * striping threshold method 3
				 * */
				if(striping_threshold_method == 3)
				{

					page_size = ( lpn_start_node + 1 )*LRUSIZE - lpn;
					lpn = ( lpn_start_node + 1 )*LRUSIZE;
					if(lpn_start_node == lpn_end_node)
					{
						page_size = page_size - ((lpn_end_node + 1)*LRUSIZE - end_lpn -1);
					}
					if(page_size <= method_para)return ;

					increase_score = 1;
				}
	
				/*
				 * striping threshold method 4
				 * */
				if(striping_threshold_method == 4)
				{
					page_size = ( lpn_start_node + 1 )*LRUSIZE - lpn;
					lpn = ( lpn_start_node + 1 )*LRUSIZE;
					if(lpn_start_node == lpn_end_node)
					{
						page_size = page_size - ((lpn_end_node + 1)*LRUSIZE - end_lpn -1);
					}
				
					increase_score = 1;	
					//page_size = page_size/8;
				
					//if(rw_count[lpn_start_node].total_page_size + page_size >= 255)
					//	rw_count[lpn_start_node].total_page_size = 255;
					//else
						rw_count[lpn_start_node].total_page_size	= rw_count[lpn_start_node].total_page_size + page_size;
				}

				/*
				 * striping threshold method 5
				 * */
				if(striping_threshold_method == 5)
				{

					page_size = ( lpn_start_node + 1 )*LRUSIZE - lpn;
					lpn = ( lpn_start_node + 1 )*LRUSIZE;
					if(lpn_start_node == lpn_end_node)
					{
						page_size = page_size - ((lpn_end_node + 1)*LRUSIZE - end_lpn -1);
					}
						
					increase_score = page_size/method_para;				
				}


				/*
				 * striping threshold method 6
				 * */
				if(striping_threshold_method == 6)
				{

					page_size = ( lpn_start_node + 1 )*LRUSIZE - lpn;
					lpn = ( lpn_start_node + 1 )*LRUSIZE;
					if(lpn_start_node == lpn_end_node)
					{
						page_size = page_size - ((lpn_end_node + 1)*LRUSIZE - end_lpn -1);
					}
	
					if(rw_count[lpn_start_node].read_count != 0)	
						increase_score = (double)rw_count[lpn_start_node].total_page_size/(double)rw_count[lpn_start_node].read_count;
					else
						increase_score = 0;

					increase_score = ((double)(rw_count[lpn_start_node].total_page_size + page_size)/(double)(1 + rw_count[lpn_start_node].read_count))\
													 - increase_score;
					rw_count[lpn_start_node].total_page_size	= rw_count[lpn_start_node].total_page_size + page_size;
				}

				if(increase_score == 0)
					return ;

				assert(striping_threshold_method < 7);
			
				//speed up the search time	
				if(rw_count[lpn_start_node].read_count == 0)
				{
					add_node_to_read_access_list(lpn_start_node,increase_score);
					increase_node_count(lpn_start_node,0);
				}
				else
				{
					increase_node_count(lpn_start_node,increase_score);
				}
				rw_count[lpn_start_node].read_count ++;
			}
		}
}


void add_and_remove_page_to_buffer_cache(ioreq_event *curr,buffer_cache *ptr_buffer_cache)
{
	static int full_cache = 0;
	unsigned int lpn,blkno,count,scount; //sector count
	ssd_t *currdisk;
	currdisk = getssd (curr->devno);
	blkno = curr->blkno;
	count = curr->bcount; //sh-- amount of  fs-block wait to be served. 
  lru_node *lru;
	
	/*add page to buffer cache*/
	while(count != 0)
	{
    int elem_num1 = lba_table[ssd_logical_pageno(blkno,currdisk)].elem_number;
    int ppn1=lba_table[ssd_logical_pageno(blkno,currdisk)].ppn;
   //printf("elen_num1=%d,ppn1=%d\n", elem_num1, ppn1);
		lpn = ssd_logical_pageno(blkno,currdisk);
		add_page_to_cache_buffer(lpn,ptr_buffer_cache);
		scount = ssd_choose_aligned_count(currdisk->params.page_size, blkno, count);
		assert(scount == currdisk->params.page_size);
		count -= scount;
		blkno += scount;
	}
	
	// mark buffer page for specific current block
	if(block_level_lru_no_parallel == 0)//���Ұ�proposed PaW
	{
		if(full_cache == 0 && ptr_buffer_cache->max_buffer_page_num < ptr_buffer_cache->total_buffer_page_num)
		{// "first" time cache was filled up.
			//initial the ptr_current_mark_node and current_mark_offset
			ptr_buffer_cache->ptr_current_mark_node = ptr_buffer_cache->ptr_head->prev;
			ptr_buffer_cache->current_mark_offset = 0;
			mark_for_all_current_block(ptr_buffer_cache);
			full_cache = 1;
      ////////////////////
      /*
      lru=ptr_buffer_cache->ptr_head;
      printf("full_cache == 0___page cache : \n");
      while(1)
      {
        printf("%d|", lru->logical_node_num);
        int i=0;
        for(i=0;i<LRUSIZE;i++)
        {
          printf("%d,", lru->page[i].lpn);
        }
        printf("\n");
        if(lru->next==ptr_buffer_cache->ptr_head)
          break;
        lru=lru->next;
      }*/
		}
		else if( full_cache == 1)
		{
			mark_for_all_current_block(ptr_buffer_cache);
      ///////////////////
      /*
      lru=ptr_buffer_cache->ptr_head;
      printf("full_cache == 1___page cache : \n");
      while(1)
      {
        printf("%d|", lru->logical_node_num);
        int i=0;
        for(i=0;i<LRUSIZE;i++)
        {
          printf("%d,", lru->page[i].lpn);
        }
        printf("\n");
        if(lru->next==ptr_buffer_cache->ptr_head)
          break;
        lru=lru->next;
      }
      */
		}
	}
	//kick page from buffer cache to flash 
	kick_page_from_buffer_cache(curr,ptr_buffer_cache);

}
void add_page_to_cache_buffer(unsigned int lpn,buffer_cache *ptr_buffer_cache)
{
	lru_node *ptr_lru_node = NULL;
	unsigned int logical_node_num = lpn/LRUSIZE;
	unsigned int offset_in_node = lpn % LRUSIZE;
	
	ptr_lru_node = ptr_buffer_cache->hash[logical_node_num % HASHSIZE];

	while(1)
	{
		if(ptr_lru_node == NULL)
			break;
		if(ptr_lru_node->logical_node_num == logical_node_num)
			break;
		if(ptr_lru_node == ptr_buffer_cache->hash[logical_node_num % HASHSIZE]->h_prev)
		{
			ptr_lru_node = NULL;
			break;
		}
		ptr_lru_node = ptr_lru_node->next;
	}
	if(ptr_lru_node == NULL)
	{
		add_a_node_to_buffer_cache(logical_node_num,offset_in_node,ptr_buffer_cache);
	}
	else
	{
		//remove the mark page int the hit node
		remove_mark_in_the_node(ptr_lru_node,ptr_buffer_cache);
		add_a_page_in_the_node(logical_node_num,offset_in_node,ptr_lru_node,ptr_buffer_cache );
	}
}
int find_page_in_cache_buffer(unsigned int lpn,buffer_cache *ptr_buffer_cache)
{
	lru_node *ptr_lru_node = NULL;
	unsigned int logical_node_num = lpn/LRUSIZE;
	unsigned int offset_in_node = lpn % LRUSIZE;
	
	ptr_lru_node = ptr_buffer_cache->hash[logical_node_num % HASHSIZE];

	while(1)
	{
		if(ptr_lru_node == NULL)
			break;
		if(ptr_lru_node->logical_node_num == logical_node_num)
			break;
		if(ptr_lru_node == ptr_buffer_cache->hash[logical_node_num % HASHSIZE]->h_prev)
		{
			ptr_lru_node == NULL;
			break;
		}
		ptr_lru_node = ptr_lru_node->next;
	}
	if(ptr_lru_node == NULL || ptr_lru_node->page[offset_in_node].exist == 0)
	{
		ptr_buffer_cache->r_miss_count ++;
		return 0;				//cache miss
	}
	else
	{
		ptr_buffer_cache->r_hit_count ++;
		return 1;				//cahce hit
	}
}

void add_a_node_to_buffer_cache(unsigned int logical_node_num,unsigned int offset_in_node,buffer_cache * ptr_buffer_cache)
{
	lru_node *ptr_node;
	ptr_node = malloc(sizeof(lru_node));
	assert(ptr_node);
	memset(ptr_node,0,sizeof(struct _lru_node));
	ptr_node->logical_node_num = logical_node_num;
	//rw intensive
	if(w_multiple == 0)
	{
		ptr_node->rw_intensive = 1;//read intensive
	}
	else if(w_multiple == 99999||w_multiple == 999999)
	{
		ptr_node->rw_intensive = 2;//write intensive
	}
	else
	{
		ptr_node->rw_intensive = 2;//write intensive
	}
	//add new node to hash table , for speed up
	if(ptr_buffer_cache->hash[logical_node_num % HASHSIZE] == NULL)
	{
		ptr_buffer_cache->hash[logical_node_num % HASHSIZE] = ptr_node;
		ptr_node->h_prev = ptr_node->h_next = ptr_node;
	}
	else
	{
		ptr_node->h_next = ptr_buffer_cache->hash[logical_node_num % HASHSIZE];
		ptr_node->h_prev = ptr_buffer_cache->hash[logical_node_num % HASHSIZE]->h_prev;
		ptr_buffer_cache->hash[logical_node_num % HASHSIZE]->h_prev->h_next = ptr_node;
		ptr_buffer_cache->hash[logical_node_num % HASHSIZE]->h_prev = ptr_node;
		ptr_buffer_cache->hash[logical_node_num % HASHSIZE] = ptr_node;
	}
	//add the node the the lru list
	if(ptr_buffer_cache->ptr_head != NULL)
	{
		ptr_node->next = ptr_buffer_cache->ptr_head;
		ptr_node->prev = ptr_buffer_cache->ptr_head->prev;
		ptr_buffer_cache->ptr_head->prev->next = ptr_node;
		ptr_buffer_cache->ptr_head->prev = ptr_node;
		ptr_buffer_cache->ptr_head = ptr_node;
	}
	else //�@�}�l�O�Ū�
	{
		ptr_buffer_cache->ptr_head = ptr_node->prev = ptr_node->next = ptr_node;
	}
	add_a_page_in_the_node(logical_node_num,offset_in_node,ptr_node,ptr_buffer_cache);
}
void add_a_page_in_the_node(unsigned int logical_node_num,unsigned int offset_in_node,lru_node *ptr_lru_node,buffer_cache *ptr_buffer_cache )
{
	
	if(ptr_lru_node->page[offset_in_node].exist != 0) // �O�_���ݩ�ۤv��LB�w�s�bcache��
	{
		ptr_buffer_cache->w_hit_count ++;
	}
	else
	{	
		ptr_buffer_cache->w_miss_count ++;
		ptr_buffer_cache->total_buffer_page_num ++;
		ptr_lru_node->buffer_page_num++;
		ptr_lru_node->page[offset_in_node].exist = 1;
		ptr_lru_node->page[offset_in_node].lpn = logical_node_num * LRUSIZE + offset_in_node;
	}
	if(ptr_lru_node == ptr_buffer_cache->ptr_head)
		return ;
	ptr_lru_node->prev->next = ptr_lru_node->next;
	ptr_lru_node->next->prev = ptr_lru_node->prev;
	
	ptr_lru_node->prev = ptr_buffer_cache->ptr_head->prev;
	ptr_lru_node->next = ptr_buffer_cache->ptr_head;
	
	ptr_buffer_cache->ptr_head->prev->next = ptr_lru_node;
	ptr_buffer_cache->ptr_head->prev = ptr_lru_node;
	
	ptr_buffer_cache->ptr_head = ptr_lru_node;
	
}


void remove_a_page_in_the_node(unsigned int offset_in_node,lru_node *ptr_lru_node,buffer_cache *ptr_buffer_cache,unsigned int verify_channel,unsigned int verify_plane)
{
	unsigned int channel_num = ptr_lru_node->page[offset_in_node].channel_num;
	unsigned int plane = ptr_lru_node->page[offset_in_node].plane;

	assert(channel_num == verify_channel);
	assert(plane == verify_plane);
	assert(ptr_lru_node->page[offset_in_node].exist == 2);

	ptr_lru_node->page[offset_in_node].exist = 0;
	ptr_lru_node->buffer_page_num --;
	ptr_buffer_cache->total_buffer_page_num --;
	
	current_block[channel_num][plane].current_mark_count --;
	current_block[channel_num][plane].current_write_offset ++;
	
	if(ptr_lru_node->buffer_page_num == 0)
	{
		remove_from_hash_and_lru(ptr_buffer_cache,ptr_lru_node);
	}
	
}

void remove_from_hash_and_lru(buffer_cache *ptr_buffer_cache,lru_node *ptr_lru_node)
{
	unsigned int logical_node_num = ptr_lru_node->logical_node_num;
	//remove node from hash 
	if(ptr_lru_node == ptr_buffer_cache->hash[logical_node_num % HASHSIZE] && ptr_lru_node->h_next == ptr_lru_node)
	{
		ptr_buffer_cache->hash[logical_node_num % HASHSIZE] = NULL;
	}
	else if(ptr_lru_node == ptr_buffer_cache->hash[logical_node_num % HASHSIZE])
	{
		ptr_buffer_cache->hash[logical_node_num % HASHSIZE] = ptr_lru_node->h_next;
		ptr_lru_node->h_prev->h_next = ptr_lru_node->h_next;
		ptr_lru_node->h_next->h_prev = ptr_lru_node->h_prev;
	}
	else 
	{
		ptr_lru_node->h_prev->h_next = ptr_lru_node->h_next;
		ptr_lru_node->h_next->h_prev = ptr_lru_node->h_prev;
	}

	//remove node from lru
	if(ptr_buffer_cache->ptr_head == ptr_lru_node && ptr_lru_node->next == ptr_lru_node)
	{
		ptr_buffer_cache->ptr_head = NULL;
	}
	else if(ptr_buffer_cache->ptr_head == ptr_lru_node)
	{
		ptr_buffer_cache->ptr_head = ptr_lru_node->next;
		ptr_lru_node->prev->next = ptr_lru_node->next;
		ptr_lru_node->next->prev = ptr_lru_node->prev;
	}
	else
	{
		ptr_lru_node->prev->next = ptr_lru_node->next;
		ptr_lru_node->next->prev = ptr_lru_node->prev;
	}
	//add in 3/2
	
	if(ptr_buffer_cache->ptr_current_mark_node == ptr_lru_node)
	{
		ptr_buffer_cache->ptr_current_mark_node = ptr_buffer_cache->ptr_current_mark_node->prev;
		ptr_buffer_cache->current_mark_offset = 0;
	}

	free(ptr_lru_node);

}
void mark_for_all_current_block(buffer_cache *ptr_buffer_cache)
{
	int i = 0,j = 0;
	for(i = 0;i < CHANNEL_NUM;i++)
	{
		for(j = 0;j < PLANE_NUM;j++)
		{   //current_mark_count: ���Ocurrent �Y�쪺 WI pages count �C �Ycurrent blk�Y�쪺�OR-intensive pages�A�N�ݭnlink list(ptr_read_intensive_buffer_page)�ӰO���o��pages(�]���L�̨Ӧۤ��P��LB)
			if(current_block[i][j].current_mark_count == 0 && current_block[i][j].ptr_read_intensive_buffer_page == NULL) //sh -- ��current ���򳣨S�Y��~
			{
				mark_for_specific_current_block(ptr_buffer_cache,i,j);
			}
		}
	}
}

void mark_for_specific_current_block(buffer_cache *ptr_buffer_cache,unsigned int channel_num,unsigned int plane)
{
     //trigger_mark_count++; //sinhome

    /*sh-- check again: no pages feed for this cur blk */
	if(current_block[channel_num][plane].ptr_read_intensive_buffer_page != NULL || current_block[channel_num][plane].current_mark_count != 0)
	return ;

	while(ptr_buffer_cache->ptr_current_mark_node->rw_intensive == 1 &&\
									 current_block[channel_num][plane].ptr_read_intensive_buffer_page == NULL)
	{
		// all of cache have be marked 
	  if(ptr_buffer_cache->ptr_current_mark_node == ptr_buffer_cache->ptr_head||ptr_buffer_cache->ptr_current_mark_node == ptr_buffer_cache->ptr_head->next)
		{
      printf("ptr_buffer_cache->ptr_current_mark_node=%d == ptr_buffer_cache->ptr_head||ptr_buffer_cache->ptr_current_mark_node == ptr_buffer_cache->ptr_head->next\n",ptr_buffer_cache->ptr_current_mark_node->logical_node_num);
      return;
    }
		//if the current mark node is read intensive
		mark_for_read_intensive_buffer(ptr_buffer_cache);
	}
	//the special channel and plane have had mark request
	if(current_block[channel_num][plane].ptr_read_intensive_buffer_page != NULL || current_block[channel_num][plane].current_mark_count != 0)
	return ;

	//mark write intensive node
	current_block[channel_num][plane].ptr_lru_node = ptr_buffer_cache->ptr_current_mark_node;
	current_block[channel_num][plane].offset_in_node = ptr_buffer_cache->current_mark_offset;
	assert(current_block[channel_num][plane].current_mark_count == 0);
	
	while(1)
	{
		//LB_to_complete_mark;
		if(ptr_buffer_cache->ptr_current_mark_node == ptr_buffer_cache->ptr_head||ptr_buffer_cache->ptr_current_mark_node == ptr_buffer_cache->ptr_head->next)
		return;

		if(ptr_buffer_cache->ptr_current_mark_node->page[ptr_buffer_cache->current_mark_offset].exist >= 2)
		{
				printf("\n");
		}
		//mark a write intensive request
		if(ptr_buffer_cache->ptr_current_mark_node->page[ptr_buffer_cache->current_mark_offset].exist == 1)
		{
			ptr_buffer_cache->ptr_current_mark_node->page[ptr_buffer_cache->current_mark_offset].exist = 2;
			ptr_buffer_cache->ptr_current_mark_node->page[ptr_buffer_cache->current_mark_offset].channel_num = channel_num;
			ptr_buffer_cache->ptr_current_mark_node->page[ptr_buffer_cache->current_mark_offset].plane = plane;
			current_block[channel_num][plane].current_mark_count ++;
		}
		ptr_buffer_cache->current_mark_offset ++;
		//when need  find new buffer page is marked
		if(ptr_buffer_cache->current_mark_offset == LRUSIZE && current_block[channel_num][plane].current_mark_count > 0)
		{	
			assert(ptr_buffer_cache->ptr_current_mark_node != ptr_buffer_cache->ptr_head);
			ptr_buffer_cache->ptr_current_mark_node = ptr_buffer_cache->ptr_current_mark_node->prev;
			ptr_buffer_cache->current_mark_offset = 0;
     //printf("3186 current_block[%d][%d].ptr_lru_node = %d\n", channel_num, plane, current_block[channel_num][plane].ptr_lru_node->logical_node_num);
			break;
		}
		else if(ptr_buffer_cache->current_mark_offset == LRUSIZE)
		{
			assert(ptr_buffer_cache->ptr_current_mark_node != ptr_buffer_cache->ptr_head);
			ptr_buffer_cache->ptr_current_mark_node = ptr_buffer_cache->ptr_current_mark_node->prev;
			ptr_buffer_cache->current_mark_offset = 0;
			
			while(ptr_buffer_cache->ptr_current_mark_node->rw_intensive == 1 &&\
									 current_block[channel_num][plane].ptr_read_intensive_buffer_page == NULL)
			{
				if(	ptr_buffer_cache->ptr_current_mark_node == ptr_buffer_cache->ptr_head||\
						ptr_buffer_cache->ptr_current_mark_node == ptr_buffer_cache->ptr_head->next)
				return ;	

				mark_for_read_intensive_buffer(ptr_buffer_cache);
			}
			if(current_block[channel_num][plane].ptr_read_intensive_buffer_page != NULL)
			return ;
			current_block[channel_num][plane].ptr_lru_node = ptr_buffer_cache->ptr_current_mark_node;
			assert(current_block[channel_num][plane].ptr_lru_node != NULL);
			current_block[channel_num][plane].offset_in_node = ptr_buffer_cache->current_mark_offset;
		}

		//when enough mark page for current block
		ssd_t *currdisk = getssd(0);
		if(current_block[channel_num][plane].current_mark_count + current_block[channel_num][plane].current_write_offset == SSD_DATA_PAGES_PER_BLOCK(currdisk))
		break;
	}
	assert(current_block[channel_num][plane].current_mark_count != 0);
}

void remove_mark_in_the_node(lru_node *ptr_lru_node,buffer_cache *ptr_buffer_cache)
{
	unsigned int i = 0;
	if(ptr_lru_node->rw_intensive == 1)
	{
		for(i = 0;i < LRUSIZE;i++)
		{
			if(ptr_lru_node->page[i].exist == 1)
			{
				break;
			}
			else if(ptr_lru_node->page[i].exist == 2)
			{
				ptr_lru_node->page[i].exist = 1;
				remve_read_intensive_page(i,ptr_lru_node);	
			}
		}
	}
	else if(ptr_lru_node->rw_intensive == 2)
	{
		for(i = 0;i < LRUSIZE;i++)
		{
			if(ptr_lru_node->page[i].exist == 1)
			{
				break;
			}
			else if(ptr_lru_node->page[i].exist == 2)
			{
				ptr_lru_node->page[i].exist = 1;
				current_block[ptr_lru_node->page[i].channel_num][ptr_lru_node->page[i].plane].current_mark_count --;
			}
		}
	}
	else
	assert(0);
	//when the hit node is the current mark node,we move the current mark node
	if(ptr_buffer_cache->ptr_current_mark_node == ptr_lru_node)
	{
		ptr_buffer_cache->ptr_current_mark_node = ptr_lru_node->prev;
		ptr_buffer_cache->current_mark_offset = 0;
	}
}

/*sh-- (1.if cache hit. 2.which to kick?  3.where to kick?)*/
void kick_page_from_buffer_cache(ioreq_event *curr,buffer_cache *ptr_buffer_cache)
{
	static unsigned int channel_num = 0,plane = 0,sta_die_num = 0,i = 0;
	unsigned int offset_in_node,logical_add;
	lru_node *ptr_lru_node;
	ssd_t *currdisk = getssd(curr->devno);
	curr->tempint2 = 0;
	/* sh-- served by cache 
	 * when the cache is not full,we return it to the parent request directly
	 * it represent we don't have to write any page to ssd
	 * */
	if(ptr_buffer_cache->total_buffer_page_num <= ptr_buffer_cache->max_buffer_page_num)
	{
   //printf("<= max_buffer_page_num\n");
		ioreq_event *child = (ioreq_event *)getfromextraq();
		child->devno = curr->devno;
    child->busno = curr->busno;
    child->flags = curr->flags;//only type is write
		child->bcount = 0;
		child->tempptr2 = curr;
		ssd_complete_parent(child,currdisk);
		addtoextraq(child);
		return ;
	}
	/*
	 * the are code is kick the page of the last block in the lru list 
	 sh--just BPLRU
	 * */
  //printf("block_level_lru_no_parallel=%d\n", block_level_lru_no_parallel);
	if(block_level_lru_no_parallel == 1)
	{
		while(ptr_buffer_cache->total_buffer_page_num > ptr_buffer_cache->max_buffer_page_num)
		{
     //printf("lru_no_parallel == 1 > max_buffer_page_num\n");
			ptr_lru_node = ptr_buffer_cache->ptr_head->prev;
      
			for(i = 0;i < currdisk->params.pages_per_block ; i ++)
			{
				if(ptr_lru_node->page[i].exist == 1)break;
			}
     //printf("ptr_lru_node = %d\n", ptr_lru_node->page[i].lpn);
			statistic.kick_write_intensive_page_count ++;

			logical_add = (ptr_lru_node->logical_node_num*LRUSIZE + i);
			/*
			 * the channel and the plane should be write
			 * */
			channel_num = (logical_add%(SSD_DATA_PAGES_PER_BLOCK(currdisk)*currdisk->params.nelements))/SSD_DATA_PAGES_PER_BLOCK(currdisk);
			plane = ((logical_add%(SSD_DATA_PAGES_PER_BLOCK(currdisk)*currdisk->params.nelements*currdisk->params.planes_per_pkg))/\
					(SSD_DATA_PAGES_PER_BLOCK(currdisk)*currdisk->params.planes_per_pkg));

			add_to_ioqueue(curr,channel_num,plane,ptr_lru_node->logical_node_num*LRUSIZE + i,0);
		
			ptr_lru_node->page[i].exist = 0;
			ptr_lru_node->buffer_page_num --;
			ptr_buffer_cache->total_buffer_page_num --;
			
			/*when the logical block is empty*/
			if(ptr_lru_node->buffer_page_num == 0)
			{
				remove_from_hash_and_lru(ptr_buffer_cache,ptr_lru_node);
			}
			current_block[channel_num][plane].flush_w_count_in_current ++;
		}
		return ;
	}
	/*
	 * when the cache size more than the max cache size,we flush the request to the ssd firstly
	 * */
	while(ptr_buffer_cache->total_buffer_page_num > ptr_buffer_cache->max_buffer_page_num)
	{
    //printf(" > max_buffer_page_num|");
	    /*sh-- our dynamic allocation policy*/
		channel_num = min_response_elem(currdisk);
		plane = max_free_page_in_plane(sta_die_num,currdisk,channel_num);
		
	//	plane = min_valid_page_in_plane(sta_die_num,currdisk,channel_num);
	//	printf("ytc94u channel_num = %d plane = %d\n",channel_num,plane);
		ptr_lru_node = current_block[channel_num][plane].ptr_lru_node;
		offset_in_node = current_block[channel_num][plane].offset_in_node;

    //printf("ptr_lru_node = %d\n", ptr_lru_node->logical_node_num);
		/*
		 * if the plane is not any mark page ,we help mark the new node 
		 * */
		if(current_block[channel_num][plane].current_mark_count == 0 && current_block[channel_num][plane].ptr_read_intensive_buffer_page != NULL)
		{
      
     //printf("* if the plane is not any mark page ,we help mark the new node|");
			statistic.kick_read_intensive_page_count ++;
			kick_read_intensive_page_from_buffer_cache(curr,channel_num,plane,ptr_buffer_cache);
			current_block[channel_num][plane].flush_w_count_in_current ++;
		
			if(current_block[channel_num][plane].ptr_read_intensive_buffer_page  == NULL)
			{
				mark_for_specific_current_block(ptr_buffer_cache,channel_num,plane);
			}
			
		}
		/*
		 * if the page already been marked 
		 * */
		else if(ptr_lru_node->page[offset_in_node].exist == 2)
		{

     //printf("* if the page already been marked|");
     //printf("ptr_lru_node = %d\n", ptr_lru_node->page[offset_in_node].lpn);
			assert(current_block[channel_num][plane].current_mark_count != 0);	
			statistic.kick_write_intensive_page_count ++;
			add_to_ioqueue(curr,channel_num,plane,ptr_lru_node->logical_node_num*LRUSIZE + offset_in_node,0);
			remove_a_page_in_the_node(offset_in_node,ptr_lru_node,ptr_buffer_cache,channel_num,plane);
			current_block[channel_num][plane].flush_w_count_in_current ++;
		
			if(current_block[channel_num][plane].current_mark_count == 0 && current_block[channel_num][plane].current_write_offset == \
																																																						SSD_DATA_PAGES_PER_BLOCK(currdisk))
			{
				current_block[channel_num][plane].current_write_offset = 0;
				mark_for_specific_current_block(ptr_buffer_cache,channel_num,plane);

			}
			else if(current_block[channel_num][plane].current_mark_count == 0)
			{
				mark_for_specific_current_block(ptr_buffer_cache,channel_num,plane);
			}
			else
			current_block[channel_num][plane].offset_in_node ++;	
		}
		else if(ptr_lru_node->page[offset_in_node].exist == 1)
		{
      printf("* if(ptr_lru_node->page[offset_in_node].exist == 1) \n");
			assert(0);
		}
		else
		{
      //printf("* else \n");
			assert(ptr_lru_node->page[offset_in_node].exist == 0);//
			current_block[channel_num][plane].offset_in_node ++;
		}
		
	}	
}
void kick_read_intensive_page_from_buffer_cache(ioreq_event *curr,unsigned int channel_num,unsigned int plane,buffer_cache *ptr_buffer_cache)
{
	lru_node *ptr_remove_node = NULL;

	current_block[channel_num][plane].ptr_read_intensive_buffer_page->ptr_self_lru_node->buffer_page_num--;
	add_to_ioqueue(curr,channel_num,plane,current_block[channel_num][plane].ptr_read_intensive_buffer_page->lpn,READ);
	printf("channel = %d plane = %d lpn = %d\n",channel_num,plane,current_block[channel_num][plane].ptr_read_intensive_buffer_page->lpn);
	ptr_buffer_cache->total_buffer_page_num --;
	if(current_block[channel_num][plane].ptr_read_intensive_buffer_page->ptr_self_lru_node->buffer_page_num == 0)
	ptr_remove_node = current_block[channel_num][plane].ptr_read_intensive_buffer_page->ptr_self_lru_node;
	
	current_block[channel_num][plane].ptr_read_intensive_buffer_page->exist = 0;
	if(current_block[channel_num][plane].ptr_read_intensive_buffer_page->next == current_block[channel_num][plane].ptr_read_intensive_buffer_page)
	{
		assert(current_block[channel_num][plane].ptr_read_intensive_buffer_page->prev == \
							current_block[channel_num][plane].ptr_read_intensive_buffer_page);	
		current_block[channel_num][plane].ptr_read_intensive_buffer_page = NULL;
	}
	else
	{
		current_block[channel_num][plane].ptr_read_intensive_buffer_page->prev->next = \
								current_block[channel_num][plane].ptr_read_intensive_buffer_page->next;
		current_block[channel_num][plane].ptr_read_intensive_buffer_page->next->prev = \
								current_block[channel_num][plane].ptr_read_intensive_buffer_page->prev;
		current_block[channel_num][plane].ptr_read_intensive_buffer_page = \
								current_block[channel_num][plane].ptr_read_intensive_buffer_page->next;
	}
	current_block[channel_num][plane].read_intenisve_mark_count--;
	if(ptr_remove_node)
	{
		remove_from_hash_and_lru(ptr_buffer_cache,ptr_remove_node);
	}
}
void add_to_ioqueue(ioreq_event* curr,unsigned int channel_num,unsigned int plane,unsigned int lpn,unsigned int rw_intensive)
{
	ssd_element *elem;
	ssd_t *currdisk;	
	ioreq_event *child = (ioreq_event *)getfromextraq();
	currdisk = getssd (curr->devno);
	elem = &currdisk->elements[channel_num];
	child->devno = curr->devno;
  child->busno = curr->busno;
  child->flags = curr->flags;//only type is write
  child->blkno = lpn * currdisk->params.page_size;
	child->bcount = currdisk->params.page_size;
	child->tempptr2 = curr;
	curr->tempint2 += child->bcount;
	child->rw_intensive = rw_intensive;
	child->plane_num = plane;
 	statistics_the_wait_time_by_striping(channel_num);
	elem->metadata.reqs_waiting ++;
	ioqueue_add_new_request(elem->queue, (ioreq_event *)child);
}
void remve_read_intensive_page(unsigned int page_offset,lru_node *ptr_lru_node)
{	
	unsigned int channel_num,plane;
	channel_num = ptr_lru_node->page[page_offset].channel_num;
	plane = ptr_lru_node->page[page_offset].plane;
	//the remove page is the last one page for current plane
	if((current_block[channel_num][plane].ptr_read_intensive_buffer_page == &ptr_lru_node->page[page_offset])&&\
									(&ptr_lru_node->page[page_offset] == ptr_lru_node->page[page_offset].next))
	{
		current_block[channel_num][plane].ptr_read_intensive_buffer_page = NULL;
		ptr_lru_node->page[page_offset].next = ptr_lru_node->page[page_offset].prev = NULL;
	}
	else if(current_block[channel_num][plane].ptr_read_intensive_buffer_page == &ptr_lru_node->page[page_offset])
	{//if the remove page position is the head of the list
		current_block[channel_num][plane].ptr_read_intensive_buffer_page = ptr_lru_node->page[page_offset].next;
		ptr_lru_node->page[page_offset].prev->next = ptr_lru_node->page[page_offset].next;
		ptr_lru_node->page[page_offset].next->prev = ptr_lru_node->page[page_offset].prev;
		ptr_lru_node->page[page_offset].next = ptr_lru_node->page[page_offset].prev = NULL;
	}
	else//direct remove the page from list
	{
		ptr_lru_node->page[page_offset].prev->next = ptr_lru_node->page[page_offset].next;
		ptr_lru_node->page[page_offset].next->prev = ptr_lru_node->page[page_offset].prev;
		ptr_lru_node->page[page_offset].next = ptr_lru_node->page[page_offset].prev = NULL;
	}
	current_block[channel_num][plane].read_intenisve_mark_count--;
}
void add_read_intensive_page_to_list(unsigned int page_offset,lru_node *ptr_lru_node)
{
	unsigned int channel_num,plane;
	channel_num = ptr_lru_node->page[page_offset].channel_num;
	plane = ptr_lru_node->page[page_offset].plane;
	if(current_block[channel_num][plane].ptr_read_intensive_buffer_page == NULL)
	{
		current_block[channel_num][plane].ptr_read_intensive_buffer_page = &ptr_lru_node->page[page_offset];
		ptr_lru_node->page[page_offset].prev = ptr_lru_node->page[page_offset].next = &ptr_lru_node->page[page_offset];
	}
	else
	{
		ptr_lru_node->page[page_offset].prev = current_block[channel_num][plane].ptr_read_intensive_buffer_page->prev;
		ptr_lru_node->page[page_offset].next = current_block[channel_num][plane].ptr_read_intensive_buffer_page;
		current_block[channel_num][plane].ptr_read_intensive_buffer_page->prev->next = &ptr_lru_node->page[page_offset];
		current_block[channel_num][plane].ptr_read_intensive_buffer_page->prev = &ptr_lru_node->page[page_offset];
	}
	current_block[channel_num][plane].read_intenisve_mark_count++;
}
int compare(const void *a,const void *b)
{
	return ((struct read_mark_plane*)a)->mark_count - ((struct read_mark_plane*)b)->mark_count;
}
void select_min_mark_current_block()
{
	int min_mark_num,min_plane,i,j;

	for(i = 0;i < params->nelements;i++)
	{
		min_mark_num = current_block[i][0].current_mark_count +current_block[i][0].read_intenisve_mark_count;
		min_plane = 0;
		for(j = 1;j < params->planes_per_pkg;j++)
		{
			if(min_mark_num > current_block[i][j].current_mark_count + current_block[i][j].read_intenisve_mark_count)
			{
				min_mark_num = current_block[i][j].current_mark_count + current_block[i][j].read_intenisve_mark_count;
				min_plane = j;
			}
		}
		min_mark_plane[i].channel_num = i;
		min_mark_plane[i].plane = min_plane;
		min_mark_plane[i].mark_count = min_mark_num;
	}
	qsort(min_mark_plane,params->nelements,sizeof(struct read_mark_plane),compare);
}
void get_min_mark_plane(unsigned int *channel_num,unsigned int *plane)
{
	int i = 0;
again:
	for(i = 0;i < params->nelements;i++)
	{
		if(min_mark_plane[i].channel_num != -1)
		{
			*channel_num = min_mark_plane[i].channel_num;
			*plane = min_mark_plane[i].plane;
			 min_mark_plane[i].channel_num = min_mark_plane[i].plane = -1;
			return ;
		}
	}
	select_min_mark_current_block();
	goto again;
}
void mark_for_read_intensive_buffer(buffer_cache *ptr_buffer_cache)
{
	int i = 0;
	unsigned int channel_num = 0,plane = 0;
/*	if(ptr_buffer_cache->ptr_current_mark_node == ptr_buffer_cache->ptr_head)
	{
			return ;
	}*/
	assert(ptr_buffer_cache->ptr_current_mark_node != ptr_buffer_cache->ptr_head);

	lru_node *ptr_lru_node = ptr_buffer_cache->ptr_current_mark_node;
	assert(ptr_lru_node->rw_intensive == 1);
	select_min_mark_current_block();	
	for(i = 0;i < LRUSIZE;i++)
	{
		if(ptr_lru_node->page[i].exist == 1)
		{
			get_min_mark_plane(&channel_num,&plane);
			ptr_lru_node->page[i].exist = 2;
			ptr_lru_node->page[i].channel_num = channel_num;
			ptr_lru_node->page[i].plane = plane;
			ptr_lru_node->page[i].ptr_self_lru_node = ptr_lru_node;
			add_read_intensive_page_to_list(i,ptr_lru_node);	
		}	
	}	
	ptr_buffer_cache->ptr_current_mark_node = ptr_buffer_cache->ptr_current_mark_node->prev;
	ptr_buffer_cache->current_mark_offset = 0;
}
/**************************************************************
 * 					 speed up the victim block search time 		      	*
 * ************************************************************/
void add_node_to_read_access_list(unsigned int logical_number,double increase_score)
{
		struct read_access_node * ptr_node = NULL;
		assert(rw_count[logical_number].ptr_read_access_node == NULL);
		ptr_node = rw_count[logical_number].ptr_read_access_node = malloc(sizeof(struct read_access_node));
		assert(ptr_node);			
		ptr_node->read_count = increase_score;
		ptr_node->logical_number = logical_number;

		if(ptr_read_access_head_node == NULL)
		{
			ptr_read_access_head_node = ptr_node; 
			ptr_node->prev = ptr_node->next = ptr_node;
		}
		else
		{
			ptr_node->next = ptr_read_access_head_node;
			ptr_node->prev = ptr_read_access_head_node->prev;
			ptr_read_access_head_node->prev->next = ptr_node;
			ptr_read_access_head_node->prev = ptr_node;
		}

}
/*
 *  *the function will increase the node count 1 and adjust the position
 *   */
void increase_node_count(unsigned int logical_number,double increase_score)
{
		struct read_access_node* ptr_node = NULL,*ptr_curr_node = NULL;
		assert(rw_count[logical_number].ptr_read_access_node);
		ptr_node = rw_count[logical_number].ptr_read_access_node;
			/*add the read score*/
		ptr_node->read_count += increase_score;
		
		if(increase_score >= 0)
		{
			if(ptr_node == ptr_read_access_head_node)
			{
				return ;
			}
			else
			{
				ptr_curr_node = ptr_node->prev;
				ptr_node->prev->next = ptr_node->next;
				ptr_node->next->prev = ptr_node->prev;
			}
			for(;;ptr_curr_node = ptr_curr_node->prev)
			{
													
				if(ptr_curr_node->read_count > ptr_node->read_count)
				{
					ptr_node->prev = ptr_curr_node;
					ptr_node->next = ptr_curr_node->next;
					ptr_curr_node->next->prev = ptr_node;
					ptr_curr_node->next = ptr_node;
					break;
				}
				if(ptr_curr_node == ptr_read_access_head_node)
				{
					ptr_node->next = ptr_curr_node;
					ptr_node->prev = ptr_curr_node->prev;
																												
					ptr_curr_node->prev->next = ptr_node;
					ptr_curr_node->prev = ptr_node;
					ptr_read_access_head_node = ptr_node;
					break;
				}
			}
		}	
		else
		{
			if(ptr_node == ptr_read_access_head_node->prev)
			{
				return ;
			}
			else
			{
				if(ptr_node == ptr_read_access_head_node)
				{
					ptr_read_access_head_node = ptr_node->next;
				}
				ptr_curr_node = ptr_node->next;
				ptr_node->prev->next = ptr_node->next;
				ptr_node->next->prev = ptr_node->prev;
				
			}
			for(;;ptr_curr_node = ptr_curr_node->next)
			{
													
				if(ptr_curr_node->read_count <= ptr_node->read_count)
				{
					ptr_node->next = ptr_curr_node;
					ptr_node->prev = ptr_curr_node->prev;
					ptr_curr_node->prev->next = ptr_node;
					ptr_curr_node->prev = ptr_node;
					break;
				}
				if(ptr_curr_node == ptr_read_access_head_node)
				{
					ptr_node->next = ptr_curr_node;
					ptr_node->prev = ptr_curr_node->prev;
																												
					ptr_curr_node->prev->next = ptr_node;
					ptr_curr_node->prev = ptr_node;
					break;
				}
			}
		}
}
/*
 * when return -1,represent there are no any node in the linked list
 * or return the victim logical block number
 * */
int remove_and_get_a_victim_logical_block(void) // decide which LB to be scattered in background
{
		struct read_access_node *ptr_node;
		unsigned int logical_number = 0;
		unsigned int max_read_count = 0;
		if(ptr_read_access_head_node == NULL)
				return -1;
		if(ptr_read_access_head_node->read_count < striping_threshold)
				return -1;

			/*
			* when there only are one node in the linked list
			* */		
		if(ptr_read_access_head_node == ptr_read_access_head_node->next)
		{
			logical_number = ptr_read_access_head_node->logical_number;
			free(ptr_read_access_head_node );
			ptr_read_access_head_node = NULL;
		}
		else if( striping_threshold_method == 4)
		{
			max_read_count = ptr_read_access_head_node->read_count;
			logical_number = ptr_read_access_head_node->logical_number;
			ptr_node = ptr_read_access_head_node;
			while(1)
			{
				ptr_node = ptr_node->next;
				if(ptr_node->read_count ==  max_read_count && rw_count[logical_number].total_page_size < rw_count[ptr_node->logical_number].total_page_size)
				{
					logical_number = ptr_node->logical_number;
				}
				else if(ptr_node->read_count !=  max_read_count || ptr_node->next == ptr_read_access_head_node)
				{
					ptr_node = rw_count[logical_number].ptr_read_access_node;
					if(ptr_node == ptr_read_access_head_node)
						ptr_read_access_head_node = ptr_read_access_head_node->next;

					ptr_node->prev->next = ptr_node->next;
					ptr_node->next->prev = ptr_node->prev;
					assert(logical_number == ptr_node->logical_number);
					free(ptr_node);
					break;
				}
			}

		}
		else
		{
			ptr_node = ptr_read_access_head_node;
			ptr_read_access_head_node = ptr_read_access_head_node->next;
			ptr_node->prev->next = ptr_node->next;
			ptr_node->next->prev = ptr_node->prev;

			logical_number = ptr_node->logical_number;
			free(ptr_node);
		}
		assert(rw_count[logical_number].ptr_read_access_node != NULL);
		rw_count[logical_number].ptr_read_access_node = NULL;
		return logical_number;
}
double remove_special_node(unsigned int logical_number)
{
		struct read_access_node *ptr_node;
		double read_count;
		if(rw_count[logical_number].ptr_read_access_node == NULL)
			return 0;
		ptr_node = rw_count[logical_number].ptr_read_access_node;

		read_count = ptr_node->read_count;

		if(ptr_node == ptr_read_access_head_node && ptr_read_access_head_node->next == ptr_read_access_head_node)
		{
			ptr_read_access_head_node = NULL;
			free(ptr_node);
		}
		else if(ptr_node == ptr_read_access_head_node)
		{
			ptr_read_access_head_node = ptr_read_access_head_node->next;
			ptr_node->prev->next = ptr_node->next;
			ptr_node->next->prev = ptr_node->prev;
			free(ptr_node);
		}
		else
		{
			ptr_node->prev->next = ptr_node->next;
			ptr_node->next->prev = ptr_node->prev;
			free(ptr_node);
		}
		assert(rw_count[logical_number].ptr_read_access_node != NULL);
		rw_count[logical_number].ptr_read_access_node = NULL;
		return read_count;
}



void show_result(buffer_cache *ptr_buffer_cache)
{

	//report the last result 
	statistic_the_data_in_every_stage();

	printf("ytc94u w_multiple = %lf ,cache_size = %d\n",w_multiple,ptr_buffer_cache->max_buffer_page_num);
	printf(" ytc94u total_live_page_cp_count2 = %d,total_gc_count = %d\n",total_live_page_cp_count2,total_gc_count );
	if(total_gc_count != 0)   	
	printf("ytc94u average live page num in  victim block = %lf\n",(double)total_live_page_cp_count2/(double)total_gc_count);
	if(GC_count_per_elem != 0)
	printf(" ytc94u GC_count_per_elem = %d,GC_count_per_plane = %d ,average = %d\n",\
								GC_count_per_elem,GC_count_per_plane,GC_count_per_plane/GC_count_per_elem);
 	if((ptr_buffer_cache->w_hit_count + ptr_buffer_cache->w_miss_count) != 0)
	printf("ytc94u write hit count = %u write miss count = %u write hit rate = %lf\n",ptr_buffer_cache->w_hit_count,ptr_buffer_cache->w_miss_count,\
		(double)ptr_buffer_cache->w_hit_count/(double)(ptr_buffer_cache->w_hit_count + ptr_buffer_cache->w_miss_count));
	if(ptr_buffer_cache->r_hit_count + ptr_buffer_cache->r_miss_count != 0)
	printf("ytc94u read hit count = %u read miss count = %u read hit rate = %lf\n",ptr_buffer_cache->r_hit_count,ptr_buffer_cache->r_miss_count,\
		(double)ptr_buffer_cache->r_hit_count/(double)(ptr_buffer_cache->r_hit_count + ptr_buffer_cache->r_miss_count));

	printf("ytc94u kick_read_intensive_page_count = %d kick_write_intensive_page_count = %d\n",\
							statistic.kick_read_intensive_page_count,statistic.kick_write_intensive_page_count);
	printf("ytc94u handle_write_count_in_activity_elem = %u\n",verify.handle_write_count_in_activity_elem);
	if(write_request_count != 0)
	printf("ytc94u write request average serve time = %lf \n",write_total_serve_time/write_request_count);
	if(read_request_count != 0)
	printf("ytc94u read request average serve time = %lf \n",read_total_serve_time/read_request_count);
	if((write_request_count + read_request_count) != 0)
	printf("ytc94u write and read request average serve time = %lf \n",(write_total_serve_time + read_total_serve_time)/(write_request_count + read_request_count));


	printf("ytc94u striping_count = %u,striping_page= %u\n",striping_count,striping_page);

	if(total_wait_striping_page_count != 0)
	{
		printf("ytc94u total_wait_striping_time = %lf ,total_wait_striping_page_count = %u\n",total_wait_striping_time,total_wait_striping_page_count);
		printf("ytc94u per striping page average wait_striping_time = %lf ,per striping  page average _wait_striping_page_count = %lf\n"\
					,total_wait_striping_time/striping_page,(double)total_wait_striping_page_count/(double)striping_page );

	}
	else
	{
		printf("ytc94u total_wait_striping_page_count == 0\n");
	}

	if(fill_block_count != 0)
		printf("ytc94u average block associate logical block = %lf\n",(double)total_logical_block_count/(double)fill_block_count);
	else
		printf("ytc94u fill_block_count == 0");
}







