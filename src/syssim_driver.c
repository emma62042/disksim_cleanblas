/*
 * DiskSim Storage Subsystem Simulation Environment (Version 4.0)
 * Revision Authors: John Bucy, Greg Ganger
 * Contributors: John Griffin, Jiri Schindler, Steve Schlosser
 *
 * Copyright (c) of Carnegie Mellon University, 2001-2008. 
 *
 * This software is being provided by the copyright holders under the
 * following license. By obtaining, using and/or copying this software,
 * you agree that you have read, understood, and will comply with the
 * following terms and conditions:
 *
 * Permission to reproduce, use, and prepare derivative works of this
 * software is granted provided the copyright and "No Warranty" statements
 * are included with all reproductions and derivative works and associated
 * documentation. This software may also be redistributed without charge
 * provided that the copyright and "No Warranty" statements are included
 * in all redistributions.
 *
 * NO WARRANTY. THIS SOFTWARE IS FURNISHED ON AN "AS IS" BASIS.
 * CARNEGIE MELLON UNIVERSITY MAKES NO WARRANTIES OF ANY KIND, EITHER
 * EXPRESSED OR IMPLIED AS TO THE MATTER INCLUDING, BUT NOT LIMITED
 * TO: WARRANTY OF FITNESS FOR PURPOSE OR MERCHANTABILITY, EXCLUSIVITY
 * OF RESULTS OR RESULTS OBTAINED FROM USE OF THIS SOFTWARE. CARNEGIE
 * MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF ANY KIND WITH RESPECT
 * TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT INFRINGEMENT.
 * COPYRIGHT HOLDERS WILL BEAR NO LIABILITY FOR ANY USE OF THIS SOFTWARE
 * OR DOCUMENTATION.
 *
 */

/*
 * A sample skeleton for a system simulator that calls DiskSim as
 * a slave.
 *
 * Contributed by Eran Gabber of Lucent Technologies - Bell Laboratories
 *
 * Usage:
 *  syssim <parameters file> <output file> <max. block number>
 * Example:
 *  syssim parv.seagate out 2676846
 */

#include <stdio.h>
#include <stdlib.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <math.h>
#include <sys/time.h>
#include <unistd.h>

#include "syssim_driver.h"
#include "disksim_interface.h"
#include "disksim_rand48.h"
extern int sum_block_count[1000000] = {100};
extern int clean_replace = 0;
extern int clean_flush1 = 0;
extern int clean_flush2 = 0;
extern long long int replace_time = 0;
extern long long int flush1_time = 0;
extern long long int flush2_time = 0;
extern int ssd_ARR = 0;
int flush_direct = 0 ;
int test_count2 = 0;
double Ref_temp = 0;
double Ref_diff = 0,diff = 0,diff1 = 0;
double Ref_dr = 0,dr = 0;
static float flush_count = 1024.0;
static float Mem = 131072.0;//202025.0;
static float dirty_ratio = 0.4;
static float dirty_count = 0.0;
static double Hitcount = 0.0,Sumcount = 0.0;
static int write_back_type; // 0->replacement 1->rule 1 2->rule 2 ( more than 30s)
static int old_dirty_time = 30 ; // 30
static int per_time = 5 ;
int read_miss = 0,read_hit = 0,write_miss = 0,write_hit = 0;
long long int evict_count = 0;
long long int count_to_buffer = 0; 
#define BLOCK 4096
#define SECTOR  512
#define BLOCK2SECTOR  (BLOCK/SECTOR)

typedef struct  {
  int n;
  double sum;
  double sqr;
} Stat;


SysTime now = 0;   /* current time */
static SysTime next_event = -1; /* next event */
static int completed = 0; /* last request was completed */
static Stat st;

// A Queue Node (Queue is implemented using Doubly Linked List)
typedef struct QNode
{
  struct QNode *prev, *next;
  long int blockNumber; // the page number stored in this QNode(±qtxtÅª¤Jªº) 
  unsigned Req_type; // 0 -> write , 1 -> read
  unsigned Dirty ; // 0 -> clean , 1 -> dirty
  unsigned write_type; // 0->replacement 1->rule 1 2->rule 2 ( more than 30s)
  unsigned size;
  unsigned devno;
  int block_count;
  long long int timestamp ;
} QNode;

// A Queue (A FIFO collection of Queue Nodes)
typedef struct Queue
{
  unsigned count; // Number of filled frames
  long long int numberOfFrames; // total number of frames
  QNode *front, *rear;
} Queue;

// A hash (Collection of pointers to Queue Nodes)
typedef struct Hash
{
  int capacity; // how many pages can be there
  QNode **array; // an array of queue nodes
} Hash;
void blockNumberCount(Queue *queue){
  QNode *block_count_Point = queue->rear;
  int i = 0;
  for(i = 0 ; i < 1000000 ; i++) sum_block_count[i] = NULL;

  while(1) {
    if(block_count_Point->Dirty == 1 ) {
      int Blk = block_count_Point->blockNumber / 64;
      sum_block_count[Blk] ++;
    }
   // printf("blockNumber[%d] = %d\n" , block_count_Point->block_count,sum_block_count[block_count_Point->block_count]);
    //if(block_count_Point != NULL )printf("blkno = %d\n",block_count_Point->blockNumber );
    if(block_count_Point == queue->front || block_count_Point == NULL) break;
    if(block_count_Point->prev != NULL) block_count_Point = block_count_Point->prev; 
    else break;
  }
  
}
//----------------------flush 1024 dirty pages---------------------
void write_back(Queue* queue , FILE *fwrite, struct disksim_interface *disksim, int on ) { 
  int flush_Number = 0;
  int extra_flush_Number = 1;
  QNode *current_Point = queue->rear;
  if(on == 1){
    //fprintf(fwrite,"write_back\n");
    while(flush_Number < 1024) {
      if(current_Point->Dirty == 1 ) {
        printf(" if(current_Point->Dirty == 1 ) \n");
        current_Point->write_type = 0;
        struct disksim_request *r = malloc(sizeof(struct disksim_request));
        r->start = now;
        r->flags = current_Point->write_type;
        r->devno = current_Point->devno;
        r->blkno = current_Point->blockNumber;
        r->bytecount = (current_Point->size) * 512;  // ssd 4096
        fprintf(fwrite,"%lf\t%ld\t%ld\t%ld\t%ld\n",now,current_Point->devno,current_Point->blockNumber,current_Point->size,current_Point->write_type);
        disksim_interface_request_arrive(disksim, now, r);
        while(next_event >= 0) {
          now = next_event;
          next_event = -1;
          disksim_interface_internal_event(disksim, now, 0);
        }
        
        printf("after while(next_event >= 0) {\n");
       // fprintf(fwrite,"%ld\t%d\n",current_Point->blockNumber,current_Point->write_type);
        current_Point->Dirty = 0;
        //printf("flush_1 = %d\n",current_Point->blockNumber);
        dirty_count -= 1.0 ;
        flush_Number += current_Point->size/8;
      
        if(current_Point != queue->front && current_Point != NULL) {
          current_Point = current_Point->prev;
        }
        else if(current_Point == queue->front && current_Point->Dirty == 0 ) 
        {
          printf("(current_Point == queue->front && current_Point->Dirty == 0 ) break;\n");
          break;
        }
        else if(current_Point == NULL) 
        {
          printf("(current_Point == NULL)  break;\n");
          break;
        }
      }
      else
      {
        current_Point = current_Point->prev;
        printf("else (current_Point->Dirty == 1 ) {\n");
      }
    }
  }else{
    clean_flush1 = 1;
    flush1_time = now;
    while(current_Point != queue->front && current_Point != NULL) {
      if(current_Point->Dirty == 1) {
          /*current_Point->write_type = 16;
          struct disksim_request *r = malloc(sizeof(struct disksim_request));
          r->start = now;
          r->flags = current_Point->write_type;
          r->devno = current_Point->devno;
          r->blkno = current_Point->blockNumber;
          r->bytecount = (current_Point->size) * 512;  // ssd 4096
          disksim_interface_request_arrive(disksim, now, r);
          while(next_event >= 0) {
          now = next_event;
          next_event = -1;
          disksim_interface_internal_event(disksim, now, 0);
        }*/
        //fprintf(fwrite,"%d\t%d\n",current_Point->blockNumber,current_Point->write_type);
        extra_flush_Number ++;
      }
      if(extra_flush_Number == 1024) break;
      else if (current_Point == queue->front) break;
      current_Point = current_Point->prev;
    }
 } 
 // blockNumberCount(queue);
}
QNode *global_flush_Point = NULL;
QNode *global_flush_MRU_Point = NULL;
QNode *global_flush_LRU_Point = NULL;
int record_flag = 0 ;
//----------------------flush 1024 location of pages -----------------------
void period_write_back(Hash *hash , Queue* queue , FILE *fwrite , struct disksim_interface *disksim ,int on) {

  
  struct  timeval tv;
  long long int local_time ;
  gettimeofday(&tv,NULL);
  local_time = tv.tv_sec;
  int diff = 0 ;
  int tec;
  float i = 1.0;
  float extra_i = flush_count;
  int extra_flush_direct ;
  
  //fprintf(fwrite,"record_flag = %d\n",record_flag);
  QNode *current_Point2 ;
  if(record_flag == 0){
    current_Point2 = queue->rear;
    if(on == 1)record_flag = 1;
  }else if(record_flag == 2){
     current_Point2 = queue->front;
     record_flag = 5;
  }else if(record_flag == 3){
     current_Point2 = queue->rear;
     record_flag = 5;
  }else{
     current_Point2 = global_flush_Point;
  }
  if(global_flush_Point == NULL){
    global_flush_Point = queue->rear;
  }
  if(global_flush_MRU_Point == queue->rear){
    current_Point2 = queue->front;
    global_flush_MRU_Point = NULL;
  }
  if(global_flush_LRU_Point == queue->front){
    current_Point2 = queue->rear;
    global_flush_LRU_Point = NULL;
  }
  if(on == 1){
    //fprintf(fwrite,"period_write_back global_flush_Point=%d record_flag = %d\n",global_flush_Point->blockNumber,record_flag);
    while(1){
      diff1 = now - ( (current_Point2)->timestamp + old_dirty_time );
      if(current_Point2->Dirty == 1 && diff1 >= 0) {
        struct disksim_request *r = malloc(sizeof(struct disksim_request));
        current_Point2->write_type = 0;
        r->start = now;
        r->flags = current_Point2->write_type;
        r->devno = current_Point2->devno;
        r->blkno = current_Point2->blockNumber;
        r->bytecount = (current_Point2->size) * 512;  // ssd 4096
        fprintf(fwrite,"%lf\t%ld\t%ld\t%ld\t%ld\n",now,current_Point2->devno,current_Point2->blockNumber,current_Point2->size,current_Point2->write_type);
        disksim_interface_request_arrive(disksim, now, r);
        while(next_event >= 0) {
          now = next_event;
          next_event = -1;
          disksim_interface_internal_event(disksim, now, 0);
        }

        
        current_Point2->Dirty = 0;
        dirty_count -=1.0;
        global_flush_Point = current_Point2;
        if(i == flush_count || current_Point2 == NULL) {break;}
        if(flush_direct == 0){
          if(current_Point2 != queue->front && current_Point2 != NULL){
            current_Point2 = current_Point2->prev;
          }else if (current_Point2 == queue->front){
            flush_direct = 1;
            global_flush_MRU_Point = current_Point2;
            record_flag = 2;
          }
        }
        if (flush_direct == 1){
          if(current_Point2 != queue->rear && current_Point2 != NULL){
            current_Point2 = current_Point2->next;
          }else if (current_Point2 == queue->rear){
            flush_direct = 0;
            global_flush_LRU_Point = current_Point2;
            record_flag = 3;
          }
        }
        //fprintf(fwrite,"ch1 flush_direct = %d\n",flush_direct);
      }else{  
        global_flush_Point = current_Point2;
        if(i == flush_count || current_Point2 == NULL) {break;}
        if(flush_direct == 0){
          if(current_Point2 != queue->front && current_Point2 != NULL){
            current_Point2 = current_Point2->prev;
          }else if (current_Point2 == queue->front){
            flush_direct = 1;
            record_flag = 2;
          }
        }
        if (flush_direct == 1){
          if(current_Point2 != queue->rear && current_Point2 != NULL){
            current_Point2 = current_Point2->next;
          }else if (current_Point2 == queue->rear){
            flush_direct = 0;
            record_flag = 3;
          }
        }
        //fprintf(fwrite,"ch2 flush_direct = %d i=%f\n",flush_direct,i);

      }
      i += 1.0;
    }
    //fprintf(fwrite,"i=%f\n",i);
  }else{
    clean_flush2 = 1;
    flush2_time = now;
    extra_flush_direct = flush_direct ;
    if(extra_flush_direct == 0 && current_Point2->prev != NULL){
      current_Point2 = current_Point2->prev;
    }else if(extra_flush_direct == 1 && current_Point2->next != NULL){
      current_Point2 = current_Point2->next;
    }
    while(1) {
      diff1 = now - ( (current_Point2)->timestamp + old_dirty_time );
      if(current_Point2->Dirty == 1 && diff1 >= 0) {
        /*struct disksim_request *extra_r = malloc(sizeof(struct disksim_request));
        current_Point2->write_type = 16;
        extra_r->start = now;
        extra_r->flags = current_Point2->write_type;
        extra_r->devno = current_Point2->devno;
        extra_r->blkno = current_Point2->blockNumber;
        extra_r->bytecount = (current_Point2->size) * 512;  // ssd 4096
        disksim_interface_request_arrive(disksim, now, extra_r);
        while(next_event >= 0) {
        now = next_event;
        next_event = -1;
        disksim_interface_internal_event(disksim, now, 0)
      }*/
      // fprintf(fwrite,"%ld\t%d\n",current_Point2->blockNumber,current_Point2->write_type);
        if(current_Point2 == queue->front || current_Point2 == queue->rear) break;
        if(extra_flush_direct == 0){
          if(current_Point2 != queue->front && current_Point2 != NULL){
            current_Point2 = current_Point2->prev;
          }
        }else if (extra_flush_direct == 1){
          if(current_Point2 != queue->rear && current_Point2 != NULL){
            current_Point2 = current_Point2->next;
          }
        }
      }else{
        if(current_Point2 == queue->front || current_Point2 == queue->rear) break;
        if(extra_flush_direct == 0){
          if(current_Point2 != queue->front && current_Point2 != NULL){
            current_Point2 = current_Point2->prev;
          }
        } 
        else if (extra_flush_direct == 1){
          if(current_Point2 != queue->rear && current_Point2 != NULL){
            current_Point2 = current_Point2->next;
          }
        }

      }
      if(extra_i == 1.0 || current_Point2 == NULL) break;
      extra_i -= 1.0;
    }
  }
 // blockNumberCount(queue);
}
// A utility function to create a new Queue Node. The queue Node
// will store the given 'blockNumber'
QNode *newQNode( unsigned blockNumber )
{
  // Allocate memory and assign 'blockNumber'
  QNode *temp = (QNode*)malloc( sizeof( QNode ) );

  temp->blockNumber = blockNumber;
  // Initialize prev and next as NULL
  temp->prev = NULL;
  temp->next = NULL;
  return temp;
}

// A utility function to create an empty Queue.
// The queue can have at most 'numberOfFrames' nodes
Queue* createQueue( long long int numberOfFrames )
{
  Queue* queue = (Queue *)malloc( sizeof( Queue ) );

  // The queue is empty
  queue->count = 0;
  queue->front = queue->rear = NULL;

  // Number of frames that can be stored in memory
  queue->numberOfFrames = numberOfFrames;
  return queue;
}

// A utility function to create an empty Hash of given capacity
Hash* createHash( long long int capacity )
{
  // Allocate memory for hash
  Hash *hash = (Hash *) malloc( sizeof( Hash ) );
  hash->capacity = capacity;

  // Create an array of pointers for refering queue nodes
  hash->array = (QNode **) malloc( hash->capacity * sizeof( QNode* ) );

  // Initialize all hash entries as empty
  int i;
  for( i = 0; i < hash->capacity; ++i )
    hash->array[i] = NULL;
  return hash;
}

// A function to check if there is slot available in memory
int AreAllFramesFull( Queue* queue )
{
  return queue->count == queue->numberOfFrames; 
}

// A utility function to check if queue is empty
int isQueueEmpty( Queue* queue )
{
  return queue->rear == NULL;
}
void replacement(Queue* queue , Hash* hash , FILE *fwrite , unsigned incoming_blockNumber ,struct disksim_interface *disksim ){
  QNode *current_Point2 = queue->rear;
  QNode *current_Point = queue->rear;
  write_back_type == 0;
  QNode *reqPage = hash->array[ incoming_blockNumber ];
  int extra_no = 0;
//  printf("incoming page = %d\n", incoming_blockNumber);
  if(current_Point2->Dirty == 1 && current_Point2->blockNumber != incoming_blockNumber && reqPage == NULL ) {
      struct disksim_request *r = malloc(sizeof(struct disksim_request));
        current_Point2->write_type = 0;
        r->start = now;
        r->flags = current_Point2->write_type;
        r->devno = current_Point2->devno;
        r->blkno = current_Point2->blockNumber;
        r->bytecount = (current_Point2->size) * 512;  // ssd 4096
        current_Point2->Dirty = 0;
        dirty_count -=1.0;
        fprintf(fwrite,"%lf\t%ld\t%ld\t%ld\t%ld\n",now,current_Point2->devno,current_Point2->blockNumber,current_Point2->size,current_Point2->write_type);
        disksim_interface_request_arrive(disksim, now, r);
        while(next_event >= 0) {
          now = next_event;
          next_event = -1;
          disksim_interface_internal_event(disksim, now, 0);
        }
                
  }
  clean_replace = 1;
  replace_time = now;
  while(current_Point != NULL && extra_no < 1) {
    if(current_Point->Dirty == 1) {
        /*current_Point->write_type = 8;
        struct disksim_request *r = malloc(sizeof(struct disksim_request));
        r->start = now;
        r->flags = current_Point->write_type;
        r->devno = current_Point->devno;
        r->blkno = current_Point->blockNumber;
        r->bytecount = (current_Point->size) * 512;  // ssd 4096
        disksim_interface_request_arrive(disksim, now, r);
        while(next_event >= 0) {
        now = next_event;
        next_event = -1;
        disksim_interface_internal_event(disksim, now, 0);
      }*/
      extra_no ++;
    }
    current_Point = current_Point->prev;
  }
  
}
// A utility function to delete a frame from queue
void deQueue( Queue* queue ){
  
  QNode *current_Point = queue->rear;
  if( isQueueEmpty( queue ) )
    return;
  if (queue->front == queue->rear) queue->front = NULL; // If this is the only node in list, then change front
 // printf("real_replacement page = %d\n", current_Point->blockNumber);
  queue->rear = queue->rear->prev;
  
  
  if (queue->rear)
    queue->rear->next = NULL;

  // decrement the number of full frames by 1
  queue->count--;
  free(current_Point);

}

// A function to add a page with given 'blockNumber' to both queue
// and hashreplacement
void Enqueue( Queue* queue, Hash* hash, unsigned blockNumber )
{
  // If all frames are full, remove the page at the rear
  if ( AreAllFramesFull ( queue ) ){
    hash->array[ queue->rear->blockNumber ] = NULL;// remove page from hash
    deQueue( queue );
  }

  // Create a new node with given page number,
  // And add the new node to the front of queue
  // newQNode¬O²£¥Í¤@­Ó¿W¥ßªº·s¸`ÂI¡A©Ò¥H¤@¶}©l¥LªºÀY§À³£¨SªF¦è
  // §â­ì¥»¦bMRUºÝªºpage²¾°Ê¨ìblnumªº¤U¤@­Ó
  // ¤@¶}©lªì©l¤Æ®É¡Aprev¬ONULL
  QNode *temp = newQNode( blockNumber  );
  temp->next = queue->front;

  // If queue is empty, change both front and rear pointers
  //¦pªG¤@¶}©l¬OªÅªº¡A¥Ø«e­n·s¼W¤@­Ónode¶i¨Ó¡A¨ºquequ¸Ì­±ªºMRU©MLRU³£¬O¦P¤@­Ó 
  if ( isQueueEmpty( queue ) )
    queue->rear = queue->front = temp;
  else // Else change the front
  {
    queue->front->prev = temp; //µ¥©ó¬O¸ò blnum->next = queue->front; ¹ïÀ³ 
    queue->front = temp;       //©Ò¥H¦¹®Éblnum³o­Ó·sªºpage´NÅÜ¦¨MRU 
  }

  // Add page entry to hash also
  hash->array[ blockNumber ] = temp;
  
  // increment number of full frames
  queue->count++;

}

// This function is called when a page with given 'blockNumber' is referenced
// from cache (or memory). There are two cases:
// 1. Frame is not there in memory, we bring it in memory and add to the front
// of queue
// 2. Frame is there in memory, we move the frame to front of queue
void ReferencePage( Queue* queue, Hash* hash, double Req_time, long int Req_devno, long int blockNumber, long int Req_size, long int Req_type, struct disksim_interface *disksim,FILE *fwrite){
  struct  timeval    tv;
  long long int local_time;
  gettimeofday(&tv,NULL);
  local_time = tv.tv_sec;
 
  

  QNode *reqPage = hash->array[ blockNumber ];
  struct disksim_request *r = malloc(sizeof(struct disksim_request));
  // the page is not in cache, bring it
  if ( reqPage == NULL ) {
    Enqueue( queue, hash, blockNumber);
    //fprintf(fwrite, "ReferencePage now=%lf\n", now);
    if(Req_type==1)
    {
      r->start = now;
      r->flags = Req_type;
      r->devno = Req_devno;
      r->blkno = blockNumber;
      r->bytecount = Req_size * 512;  // ssd 4096
      fprintf(fwrite,"%lf\t%ld\t%ld\t%ld\t%ld\n",now,Req_devno,blockNumber,Req_size,Req_type);
      disksim_interface_request_arrive(disksim, now, r);
      while(next_event >= 0) {
        now = next_event;
        next_event = -1;
        disksim_interface_internal_event(disksim, now, 0);
      }
      //fprintf(fwrite,"%lf\t%ld\t%ld\t%ld\t%ld\n",now,Req_devno,blockNumber,Req_size,Req_type);
    }
    QNode *reqPage = hash->array[ blockNumber ];
    reqPage->Req_type = Req_type;
    reqPage->size = Req_size;
    reqPage->devno = Req_devno;
    reqPage->timestamp = now;
    reqPage->block_count = (blockNumber / 64 ) ;
    if (reqPage->Req_type == 1 ){
      reqPage->Dirty = 0;
    }else{
      reqPage->Dirty = 1;
      dirty_count += 1.0;
    }
  } else if (reqPage == queue->front){ // page is there and at front, change pointer
    if(Req_type == 0){  
      if(reqPage->Req_type == 1 ){  
        reqPage->Req_type = Req_type;  
        reqPage->Dirty = 1;
        dirty_count += 1.0;
      }else{
        reqPage->Req_type = Req_type;  
        if(reqPage->Dirty != 1){
          reqPage->Dirty = 1; 
          dirty_count += 1.0; 
        }
      }       
    }else{                
      if(reqPage->Req_type == 1 ){    
        reqPage->Req_type = Req_type;
      }else{              
        reqPage->Req_type = Req_type;  
      }
    }
    
    Hitcount++;
  }else if (reqPage != queue->front){ // page is there and not at front, change pointer
    if(Req_type == 0){  //if type of new request is 0(write) , update type of the new reqest , //and dirty always is true;
      if(reqPage->Req_type == 1 ){  
        reqPage->Req_type = Req_type;  
          reqPage->Dirty = 1;
          dirty_count += 1.0;  // 0->1 ,so dirty count ++
      }else{
        reqPage->Req_type = Req_type;  
        if(reqPage->Dirty != 1){
          reqPage->Dirty = 1;
          dirty_count += 1.0;
        }
      }       
    }else{                 //if type of new request is 1(read) , and last state is 1(read) , it's clean page
      if(reqPage->Req_type == 1 ){    
        reqPage->Req_type = Req_type;
        reqPage->Dirty = 0;
      }else{               //if type of new request is 1(read) , but last state is 0(write) , it's dirty page
        reqPage->Req_type = Req_type;   
      }
    }
    
    Hitcount++;
    // Unlink rquested page from its current location
    // in queue.
    reqPage->prev->next = reqPage->next;
    if (reqPage->next)
      reqPage->next->prev = reqPage->prev;

    // If the requested page is rear, then change rear
    // as this node will be moved to front
    if (reqPage == queue->rear){
      queue->rear = reqPage->prev;
      queue->rear->next = NULL;
    }

    // Put the requested page before current front
    reqPage->next = queue->front;
    reqPage->prev = NULL;

    // Change prev of current front
    reqPage->next->prev = reqPage;

    // Change front to the requested page
    queue->front = reqPage;
    if(Req_type == 0 ){
      if(diff == 0) Ref_diff = now + 4 ;
      else Ref_diff = diff -1;
      Ref_temp = 1 ;
      Ref_dr = now - Ref_diff;
      if( Ref_dr >=0 ){
             printf("before pwh 0\n");

       period_write_back(hash, queue ,fwrite,disksim,0);
             printf("after pwh 0\n");

      }
      if((dirty_count/Mem) >= (dirty_ratio - 0.01)) {
             printf("before wh 0\n");

          write_back(queue ,fwrite,disksim,0);
             printf("after wh 0\n");

      }
    }
  }
}




void
panic(const char *s)
{
  perror(s);
  exit(1);
}


void
add_statistics(Stat *s, double x)
{
  s->n++;
  s->sum += x;
  s->sqr += x*x;
}


void
print_statistics(Stat *s, const char *title)
{
  double avg, std;

  avg = s->sum/s->n;
  std = sqrt((s->sqr - 2*avg*s->sum + s->n*avg*avg) / s->n);
  printf("%s: n=%d average=%f std. deviation=%f\n", title, s->n, avg, std);
  printf("read miss = %d\n", read_miss);
  printf("read hit = %d\n", read_hit);
  printf("write miss = %d\n", write_miss);
  printf("write hit = %d\n", write_hit);
  printf("all count = %lld\n",count_to_buffer);
  printf("evict_count = %lld\n", evict_count);
}


/*
 * Schedule next callback at time t.
 * Note that there is only *one* outstanding callback at any given time.
 * The callback is for the earliest event.
 */
void
syssim_schedule_callback(disksim_interface_callback_t fn, 
       SysTime t, 
       void *ctx)
{
  next_event = t;
}


/*
 * de-scehdule a callback.
 */
void
syssim_deschedule_callback(double t, void *ctx)
{
  next_event = -1;
}


void
syssim_report_completion(SysTime t, struct disksim_request *r, void *ctx)
{
  completed = 1;
  now = t;
  add_statistics(&st, t - r->start);
}


int main(int argc, char *argv[]) {
  int i;
  int nsectors = 1000;
  struct stat buf;
  struct disksim_request r;
  struct disksim_interface *disksim;
 
  struct  timeval    tv;
  long long int Global_time ;
  int temp = 0;
  double time;
  int devno;
  int blnum=0,R_W=0,size;
  int temp_2 = 0 ;
  
  float evict_time;
  long int evict_devno , evict_blnum , evict_size , evict_flags;
  //printf("tv_sec:%ld\n",Global_time);
  printf("<<<ssd_ARR=%d>>>\n",ssd_ARR);
  FILE *fwrite = fopen("/home/osnet/disksim_cleanblas/flush.txt","w");
  //FILE *fread = fopen("/home/osnet/num_iozone.txt","r");
  FILE *fread = fopen("/home/osnet/IP2GP_multi1.txt","r");
  //FILE *evict_fread = fopen("/home/osnet/Desktop/disksim2/src/BPLRU/iozone/2048","r");

  Queue *q = createQueue( Mem ); // Let cache can hold x pages
  Hash *hash = createHash( 100000000 );// Let 10 different pages can be requested (pages to be referenced are numbered from 0 to 9 )

 if (argc != 4 ) {
    fprintf(stderr, "usage: %s <param file> <output file> <#sectors>\n",
      argv[0]);
    exit(1);
  }

  if (stat(argv[1], &buf) < 0)
    panic(argv[1]);

  disksim = disksim_interface_initialize(argv[1], 
           argv[2],
           syssim_report_completion,
           syssim_schedule_callback,
           syssim_deschedule_callback,
           0,
           0,
           0);

  if (fread == NULL)
        perror ("Error opening file");
    else {
      int times=0;
       while(fscanf(fread,"%lf%ld%ld%ld%ld",&time,&devno,&blnum,&size,&R_W)!= EOF){
         // printf("%f\n",dirty_count );
        if(now<=time)
          now=time;
        //fprintf(fwrite, "^now=%lf\n", now);
        times++;
          printf("request=%d\n", times );
          Sumcount++; 
          test_count2 ++ ;
          if(temp == 0){
            diff = now + per_time ;
            temp = 1 ;
          }
          if ( AreAllFramesFull ( q ) ){
            replacement(q , hash, fwrite , blnum , disksim);
          }
          //fprintf(fwrite, "^^now=%lf\n", now);
          ReferencePage( q, hash, time, devno, blnum, size, R_W, disksim,fwrite);
          //fprintf(fwrite, "^^^now=%lf\n", now); 
          QNode *block_count_Point = q->rear;
          int i = 0;
          for(i = 0 ; i < 1000000 ; i++) sum_block_count[i] = 0;
          while(1) {
            if(block_count_Point->Dirty == 1 ) {
              int Blk = ((block_count_Point->blockNumber/8) / 64 ) ;
              sum_block_count[Blk] ++;
            }
            if(block_count_Point == q->front || block_count_Point == NULL) break;
            if(block_count_Point->prev != NULL) block_count_Point = block_count_Point->prev; 
            else break;
          }
          if((dirty_count/Mem) >= dirty_ratio){ //flush_1 number of dirty more than dirty ratio , exe flush 
             printf("before wh\n");
             write_back(q ,fwrite,disksim,1);
             printf("after wh\n");
            QNode *block_count_Point = q->rear;
            int i = 0;
            for(i = 0 ; i < 1000000 ; i++) sum_block_count[i] = 0;
            while(1) {
              if(block_count_Point->Dirty == 1 ) {
                int Blk = ((block_count_Point->blockNumber/8) / 64 ) ;
                sum_block_count[Blk] ++;
              }
              if(block_count_Point == q->front || block_count_Point == NULL) break;
              if(block_count_Point->prev != NULL) block_count_Point = block_count_Point->prev; 
              else break;
            }
          }
          
          dr = now - diff;
          //fprintf(fwrite, "dr = %lf now =%lf - diff=%lf;\n", dr,now,diff);
         // printf("test_count2 = %d\n", test_count2 );
          if( dr >= 0) { // per 5 second to wake up 
            temp = 0;
            printf("before pwh\n");
            period_write_back(hash, q,fwrite,disksim,1);
            printf("after pwh\n");
            QNode *block_count_Point = q->rear;
            int i = 0;
            for(i = 0 ; i < 1000000 ; i++) sum_block_count[i] = 0;
            while(1) {
              if(block_count_Point->Dirty == 1 ) {
                int Blk = ((block_count_Point->blockNumber/8) / 64 ) ;
                sum_block_count[Blk] ++;
              }
              if(block_count_Point == q->front || block_count_Point == NULL) break;
              if(block_count_Point->prev != NULL) block_count_Point = block_count_Point->prev; 
              else break;
            }
          }
         
       } 
        
    }
    int kk = 0;printf("kk = %d \n", kk);
  // Let us print cache frames after the above referenced pages
/*
 while(fscanf(evict_fread,"%f%ld%ld%ld%ld",&evict_time,&evict_devno,&evict_blnum,&evict_size,&evict_flags)!= EOF){
  //kk++;
  //printf("kk = %d \n", kk);
  struct disksim_request *r = malloc(sizeof(struct disksim_request));
  // the page is not in cache, bring it
    r->start = evict_time;
    r->flags = evict_flags;
    r->devno = evict_devno;
    r->blkno = evict_blnum;
    r->bytecount = evict_size;  
    disksim_interface_request_arrive(disksim, evict_time, r);
    while(next_event >= 0) {
      now = next_event;
      next_event = -1;
      disksim_interface_internal_event(disksim, now, 0);
    }
  }*/
  int j=0;
 
  /*while(j<=1000){
    QNode *cur = hash->array[j];
    if(cur!= NULL)
     printf("blkno = %d , invalid = %d\n",cur->blockNumber ,cur->invalid);
     cur = cur->next;
    j++;
  }*/
 /* while(print_cur != NULL){
        printf ("%d\n", print_cur->F_blockNumber);
        print_cur = print_cur->F_next;
      }*/
 // printf ("invalid =%d\n", cur->invalid);
  printf("<<<ssd_ARR=%d>>>\n",ssd_ARR);
  printf("Sumcount = %.0lf,Hitcount = %.0lf Hit = %.2f\n",Sumcount,Hitcount,(Hitcount/Sumcount)*100.0);
  
//-----------------------------------------------------------------------------------------------------------------------
 

  /* NOTE: it is bad to use this internal disksim call from external... */
  DISKSIM_srand48(1);

 /* for (i=0; i < 1; i++) {
    r.start = now;
    r.flags = DISKSIM_READ;
    r.devno = 0;

    // NOTE: it is bad to use this internal disksim call from external... 
    r.blkno = BLOCK2SECTOR*(DISKSIM_lrand48()%(nsectors/BLOCK2SECTOR));
    r.bytecount = BLOCK;
    completed = 0;
    disksim_interface_request_arrive(disksim, now, &r);

    // Process events until this I/O is completed 
    

    if (!completed) {
      fprintf(stderr,
        "%s: internal error. Last event not completed %d\n",
        argv[0], i);
      exit(1);
    }
  }*/
 
  disksim_interface_shutdown(disksim, now);
  print_statistics(&st, "response time");
  //fclose(evict_fread);
  //printf("evict_fread\n");
  fclose(fread);
  printf("fread\n");
  fclose(fwrite);
  printf("fwrite\n");
  exit(0);
}
