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
#define DEBUG

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


/* One block of memory with Header and payload */
typedef struct Block {
    struct Block *prev,         /* Pointer to prev block    */
                 *next;         /* Pointer to next block    */
    size_t bsize,               /* Block size = header + payload */
           padd;
    long data[1];               /* Payload */
} Block;

static Block *head_list = NULL,
             *tail_list = NULL;
static size_t bsize_of_minblock= 0;


/* rounds up to the nearest multiple of ALIGNMENT */
static size_t
align_size ( size_t size ){
    size_t bsize = size + sizeof(Block) - sizeof(long);
    if ( bsize & 0xF )
        bsize = ((bsize >> 4) + 1 ) << 4;
    return bsize;
}

static Block *
extend_heap (size_t bsize){
    size_t pagesize = mem_pagesize();

    Block * bp = NULL;

    if ( bsize != pagesize )
        bsize = (bsize/pagesize+1)*pagesize;

    Block * p = (Block*) mem_sbrk ( bsize );
    if ( p != (Block*)-1 ){

        if ( tail_list ){
            p -> prev             = tail_list;
            tail_list             = p;
        }
        else {
            p -> prev             = NULL;
            head_list = tail_list = p;
        }

        p -> bsize = bsize;
        p -> next      = NULL;

        bp = p;
    }

    return bp;
}

/*
 * Initialize: returns false on error, true on success.
 */
bool 
mm_init(void){

    head_list = tail_list = NULL;

    bsize_of_minblock = align_size (1);

    return true;
}


static Block*
get_next_block ( Block * bp ){
    return (Block*)((char*)bp + (bp -> bsize & ~1ull));
}

static void*
find_fit(size_t bsize){
    Block * bp;
    for ( bp = head_list; bp; bp = bp -> next ){
        if ( !(bp -> bsize & 1) && bp -> bsize >= bsize )
            break;
    }
    return bp;
}

static void
alloc_block ( Block * bp, size_t bsize ){
    Block *bn;
    size_t ds = bp -> bsize - bsize;

    bp -> bsize = bsize;

    if (  ds >= bsize_of_minblock ){               /* Split block if possible */
        bn = get_next_block ( bp );

        bn -> bsize = ds;
        bn -> prev      = bp;
        bn -> next      = bp -> next;
        bp -> next      = bn;

        if ( tail_list == bp )
            tail_list = bn;
    }

    bp -> bsize |=1;
}

static Block*
get_block_ptr ( void *ptr ){
    return (Block*)((char*)ptr - sizeof(Block) + sizeof(long));
}

static size_t
get_data_size ( Block * bp ){
    size_t s =  bp -> bsize + sizeof(long);
    return s - sizeof(Block); 
}
 

/*
 * malloc
 */
void* 
malloc(size_t size){
    Block *bp = NULL; 

    if (size){

        size_t bsize = align_size ( size );

        bp = find_fit ( bsize );

        if ( !bp )
            bp = extend_heap ( bsize );

        if ( bp )
            alloc_block ( bp, bsize );
    }

    mm_checkheap (__LINE__);

    return (void*)&bp -> data[0];
} 

/*
 * free
 */
void 
free(void* ptr){
    Block * bp = get_block_ptr ( ptr );


    bool prev_free = (bp -> prev && !(bp -> prev -> bsize & 1 )) ? true : false;
    bool next_free = (bp -> next && !(bp -> next -> bsize & 1 )) ? true : false;

    bp -> bsize &= ~1ull;

    if (  prev_free && !next_free ){
        bp -> prev -> bsize += bp -> bsize;
        bp -> prev -> next   = bp -> next;
        if ( bp -> next )
            bp -> next -> prev = bp -> prev;
    }
    else
    if ( !prev_free && next_free  ){
        bp -> bsize += bp -> next -> bsize;
        if ( bp -> next -> next )
            bp -> next -> next -> prev = bp;
        bp -> next   = bp -> next -> next;
    }
    else
    if (  prev_free && next_free  ){
        bp -> prev -> bsize += bp -> bsize + bp -> next -> bsize;
        bp -> prev -> next = bp -> next -> next;
        if ( bp -> next -> next )
            bp -> next -> next -> prev = bp -> prev;
    }
    else 
    if ( !prev_free && !next_free ){
    }

    mm_checkheap(__LINE__);

}

/*
 * realloc
 */
void* 
realloc(void* oldptr, size_t size) {
    size_t oldsize;
    void *newptr;

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
    mm_checkheap (__LINE__ );
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
    printf("bp %p: %s {prev: %p, next: %p} bsize=%llu\n",bp,(bp -> bsize & 1) ? "A":"F", bp -> prev, bp -> next, bp -> bsize & ~1ull);
}

static void 
checkblock(void *bp){
    (void)bp;
}
/*
 * mm_checkheap
 */
bool 
mm_checkheap(int lineno){
    (void)lineno;
    Block * pb; 
    for ( pb = head_list; pb; pb = pb -> next ) {
        if ( pb -> next &&  (Block*)((char*)pb + (pb -> bsize&~1ull)) > pb -> next ){
            printf("%d\n",__LINE__); for ( pb = head_list; pb; pb = pb -> next ) printblock(pb);
            abort();
            return false;
        }
        if ( pb -> prev && pb -> prev < (Block*)0x1000 ){
            printf("%d\n",__LINE__); for ( pb = head_list; pb; pb = pb -> next ) printblock(pb);
            abort();
            return false;
        }
        if ( pb -> next && pb -> next < (Block*)0x1000 ){
            printf("%d\n",__LINE__); for ( pb = head_list; pb; pb = pb -> next ) printblock(pb);
            abort();
            return false;
        }
    }


    return true;
}
