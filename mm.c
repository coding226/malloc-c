/*
 * mm.c
 *
 * Name: iamgives@gmail.com 
 *
 * Dynamic memory allocator.
 * 
 * 
 *
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

/*
 * If you want to enable your debugging output and heap checker code,
 * uncomment the following line. Be sure not to have debugging enabled
 * in your final submission.
 */
//#define DEBUG

#ifdef DEBUG
/* When debugging is enabled, the underlying functions get called */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated */
#define dbg_printf(...)
#define dbg_assert(...)
#endif /* DEBUG */

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* DRIVER */

static void printlist(void);

/* One block of memory with Header and payload */
typedef struct Block {
    struct Block *next_free,    /* Pointer to next free block    */
                 *next;         /* Pointer to next block         */
    long   data[1];             /* Payload */
    size_t bsize;               /* Block size in the end of the block */
} Block;

#define HEADER_SIZE (sizeof(Block)-sizeof(long))

static Block *head_list = NULL, /* head list of blocks */
             *tail_list = NULL, /* tail list of blocks */
             *head_free = NULL; /* head list of free blocks */

static size_t bsize_of_minblock = 0,    /* minimal size of block    */
              bsize_of_allblock = 0;    /* total size of all blocks */


/* rounds up the size to the nearest multiple of ALIGNMENT */
static size_t
align_size ( size_t size ){
    size_t bsize = size + HEADER_SIZE;
    if ( bsize & 0xF )
        bsize = ((bsize >> 4) + 1uLL ) << 4;
    return bsize;
}

/*
 * Initialize: returns false on error, true on success.
 */
bool 
mm_init(void){

    head_list = tail_list = head_free = NULL;

    bsize_of_allblock = 0;
    bsize_of_minblock = align_size (1);

    dbg_printf("\n ******** mm_init ******************\n\n");

    return true;
}



/* Store size of the block at the end of the block */
static void
set_block_size ( Block * bp, size_t bsize ){
    *((size_t*)bp + bsize/sizeof(size_t) - 1) = bsize;
}

/* Return size of the block */
static size_t
get_block_size ( Block * bp ){
    size_t bsize;
    if ( bp == tail_list ){
        bsize = *((size_t*)head_list + bsize_of_allblock/sizeof(size_t) - 1);
    }
    else {
        bsize = *((size_t*)bp -> next - 1);
    }
    return bsize & ~1ull;
}

/* Check if the block free*/
static int
is_block_free ( Block * bp, size_t bsize ){
    return !((*((size_t*)bp + bsize/sizeof(size_t) - 1)) & 1 );
}

/* Mark the block as free */
static void
set_block_free ( Block * bp, size_t bsize ){
    size_t
    *psize = (size_t*)bp + bsize/sizeof(size_t) - 1;
    *psize ^= 1;
}

/* Mark the block as no free */
static void
set_block_allc ( Block * bp, size_t bsize ){
    size_t
    *psize = (size_t*)bp + bsize/sizeof(size_t) - 1;
    *psize |= 1;
}

/* Get prev block by size */
static Block*
prev_block ( Block * bp ){
    size_t prev_size = *((size_t*)bp-1) & ~1ull;
    return (Block*)((char*)bp - prev_size);
}

/* Get next block by size */
static Block*
next_block ( Block * bp ){
    return (Block*)((char*)bp + get_block_size(bp));
}

/* Find the first  fit-free block */
static Block*
find_fit(size_t bsize, Block **prev_free){
    Block * bp;
    for ( bp = head_free, *prev_free = NULL; bp; bp = bp -> next_free ){
        size_t bp_bsize = get_block_size ( bp );
        if ( bp_bsize >= bsize )
            break;
        *prev_free = bp;
    }
    return bp;
}

/* Split free block by two if possible  */
static Block*
split_block ( Block * bp, size_t bsize, size_t * new_bsize ){
    Block *bp_new  = (Block*)((char*)bp + bsize);

    size_t old_size = get_block_size(bp),
           new_size = old_size - bsize;

    *new_bsize = old_size;
    /* Size of the new block must be greater than min block size */
    if (  new_size >= bsize_of_minblock ){               

        /* fix size of blocks */
        set_block_size ( bp    , bsize    );
        set_block_size ( bp_new, new_size );

        bp_new -> next      = bp -> next;
        bp_new -> next_free = bp -> next_free;

        bp -> next      = bp_new;
        bp -> next_free = bp_new;

        if ( tail_list == bp )
            tail_list = bp_new;

        *new_bsize = bsize;
    }

    return bp;
}

/* Mark a free block as no free */
static void
alloc_block ( Block * bp, size_t bsize, Block * prev_free ){

    set_block_allc ( bp, bsize );

    if ( prev_free ){
        prev_free -> next_free = bp -> next_free;
    }

    if ( head_free == bp )
        head_free = bp -> next_free;

    //bp -> next_free = NULL;
}

/* Return start of the block by pointer (from malloc, free) */
static Block*
get_block_ptr ( void *ptr ){
    return (Block*)((char*)ptr - 2*sizeof(void*));
}

/* Return size of data in the Block */
static size_t
get_data_size ( Block * bp ){
    size_t s =  get_block_size(bp);
    return s - HEADER_SIZE; 
}

/* Extend the process heap */
static Block *
extend_heap (size_t bsize, Block * prev_free){
    /* min alloc equal pagesize */
    size_t pagesize = 4096;//mem_pagesize();

    bsize = (bsize/pagesize+1)*pagesize;

    Block* bp = (Block*) mem_sbrk ( bsize );
    if ( bp != (Block*) -1 ){
        if ( tail_list ){
            //size_t tail_bsize = get_block_size ( tail_list);
            //if ( !is_block_free ( tail_list, tail_bsize) ){

                bp -> next      = NULL;
                bp -> next_free = NULL;

                set_block_size ( bp, bsize );

                tail_list -> next = bp;
                tail_list = bp;

                if ( prev_free )
                    prev_free -> next_free = bp;
                else
                    head_free = bp;

            //}
            //else {
            //    set_block_size ( tail_list, bsize + tail_bsize );
            //    bp = tail_list;
            //}
        }
        else{
            head_list = tail_list = head_free = (Block*)bp;
            tail_list -> next      = NULL;
            tail_list -> next_free = NULL;
            set_block_size ( bp, bsize );
        }

        bsize_of_allblock += bsize;
    }
    else
        bp = NULL;

    return bp;
}

 

/*
 * malloc
 */
void* 
malloc(size_t size){
    Block *bp = NULL, *prev_free = NULL; 
    //mm_checkheap (__LINE__);
    if (size){
        /* bsize is multiple 16 */
        size_t bsize = align_size ( size );
        /* search the first free block */
        bp = find_fit ( bsize, &prev_free );

        /* if no free block expand the heap */
        if ( !bp ){
            bp = extend_heap ( bsize, prev_free );
        }

        if ( bp ){
            size_t new_bsize;
            /* try to split */
            split_block ( bp, bsize, &new_bsize );
            /* mark as no free */
            alloc_block ( bp, new_bsize, prev_free );
        }

        dbg_printf("\nmalloc: %p  bp %p size=%ld bsize=%ld\n",&bp->data[0],bp,size,bsize);
    }

    mm_checkheap (__LINE__);

    return bp ? &bp -> data[0] : NULL;
} 

/* Find a previous free block than point at the block */
static Block*
find_prev_free ( Block * bp ){
    Block* prev_free = NULL, *p;

    for ( p = head_free; p; p = p -> next_free ){
        if ( p == bp )
            break;
        prev_free = p;
    }

    return prev_free;
}

/*
 * free
 */
void 
free(void* ptr){
    Block * bp = get_block_ptr ( ptr ),
          * bp_prev = NULL,
          * bp_next = NULL;
    size_t  sz_prev = 0,
            sz_next = 0;

    bool prev_free = false, next_free = false;

    dbg_printf("\nfree  : %p  bp %p\n",ptr,bp);

    if ( head_list != bp ){
        bp_prev   = prev_block (bp);
        sz_prev   = get_block_size ( bp_prev );
        prev_free = is_block_free  ( bp_prev, sz_prev );
    }
    if ( tail_list != bp ){
        bp_next   = bp -> next;
        sz_next   = get_block_size ( bp_next );
        next_free = is_block_free  ( bp_next, sz_next );
    }

    size_t bsize = get_block_size ( bp );

    set_block_free ( bp, bsize );

    /* merge with the previous */
    if (  prev_free && !next_free ){

        set_block_size ( bp_prev, sz_prev + bsize );

        bp_prev -> next = bp -> next;

        if ( bp == tail_list )
            tail_list = bp_prev;
    }
    else
    /* merge with the next */
    if ( !prev_free && next_free  ){

        set_block_size ( bp, sz_next + bsize );

        bp -> next = bp_next -> next;

        if ( bp_next == tail_list )
            tail_list = bp;

        Block* prev_free = find_prev_free ( bp_next );

        if ( prev_free )
            prev_free -> next_free = bp;
        else
        if ( head_free == bp_next )
            head_free = bp;

        bp -> next_free = bp_next -> next_free;

    }
    else
    /* merge with the previous and the next */
    if (  prev_free && next_free  ){

        set_block_size ( bp_prev, sz_prev + sz_next + bsize );

        bp_prev -> next = bp_next -> next;

        if ( bp_next == tail_list )
            tail_list = bp_prev;

        Block* prev_free = find_prev_free ( bp_next );
        if ( prev_free )
            prev_free -> next_free = bp_next -> next_free;
        else
        if ( head_free == bp_next )
            head_free = bp_next -> next_free;
    }
    else 
    if ( !prev_free && !next_free ){
        if ( head_free )
            bp -> next_free = head_free;
        else
            bp -> next_free = NULL;
        head_free = bp;
    }

    mm_checkheap ( __LINE__ );
}

/*
 * realloc
 */
void* 
realloc(void* oldptr, size_t size) {
    size_t oldsize;
    void *newptr;

    mm_checkheap (__LINE__ );

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        free(oldptr);
        return NULL;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(oldptr == NULL) {
        return malloc(size);
    }

    Block * bp = get_block_ptr ( oldptr ); 
    /*
    TODO: add merge with next free block

    size_t new_bsize = align_size ( size );

    if ( bp -> next && bp -> next -> bsize + bp -> bsize >= new_bsize ){    
    }
    */

    newptr = malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return 0;
    }

    //Block * bp_new = get_block_ptr ( newptr );

    /* Copy the old data. */
    oldsize = get_data_size ( bp );
    if(size < oldsize) oldsize = size;
    memcpy(newptr, oldptr, oldsize);

    /* Free the old block. */
    free(oldptr);

    mm_checkheap (__LINE__ );

    return newptr;
}
/*
 * calloc
 * This function is not tested by mdriver, and has been implemented for you.
 */
void* 
calloc(size_t nmemb, size_t size){
    void* ptr;
    size *= nmemb;
    ptr = malloc(size);
    if (ptr) {
        memset(ptr, 0, size);
    }
    return ptr;
}
/*
 * Returns whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool 
in_heap(const void* p){
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

static void 
printblock(Block *bp){
    if (bp){
        size_t bsize = get_block_size ( bp );
        bool   bfree = is_block_free  ( bp, bsize );
    //printf("p %p - bp %p: %s {next: %p, next_free: %p} bsize=%llu\n",&bp->data[0],bp,(bp->bsize&1)?"A":"F",bp -> prev, bp -> prev_free, bp -> next_free, bp -> bsize & ~1ull);
        printf("bp %p: %s {next: %p, next_free: %p} bsize=%lu\n",bp,(bfree)?"F":"A",bp -> next, bp -> next_free, bsize );
    }
}

static void
printlist(void){
    for ( Block * pb = head_list; pb; pb = pb -> next ) printblock(pb);
}

/*
 * mm_checkheap
 */
bool 
mm_checkheap(int lineno){

    #ifdef DEBUG
#if 0
    Block * pb; 
    for ( pb = head_list; pb; pb = pb -> next ) {
        if ( pb -> next &&  (Block*)((char*)pb + (pb -> bsize&~1ull)) > pb -> next ){
            printf("%d overflow bp=%p\n",lineno,pb); for ( pb = head_list; pb; pb = pb -> next ) printblock(pb); abort();
            return false;
        }
        if ( pb -> next && pb -> next -> prev != pb ){
            printf("%d order bp=%p\n",lineno,pb); for ( pb = head_list; pb; pb = pb -> next ) printblock(pb); abort();
            return false;
        }
        if ( pb -> prev && pb -> prev -> prev == pb -> prev ){
            printf("%d duplicate prev=%p\n",lineno,pb->prev); for ( pb = head_list; pb; pb = pb -> next ) printblock(pb); abort();
            return false;
        }
        if ( pb -> prev && pb -> prev -> next == pb -> next ){
            printf("%d duplicate next=%p\n",lineno,pb->next); for ( pb = head_list; pb; pb = pb -> next ) printblock(pb); abort();
            return false;
        }
        if ( !pb -> next && pb != tail_list ){
            printf("%d lost tail! tail=%p list_last=%p\n",lineno,tail_list,pb); for ( pb = head_list; pb; pb = pb -> next ) printblock(pb); abort();
        }
    }
#endif
    { printf("line: %d head_list: %p  tail_list: %p  head_free: %p\n",lineno,head_list,tail_list,head_free); printlist(); }
    #endif

    return true;
}

