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
    struct Block *prev,         /* Pointer to prev block    */
                 *next;         /* Pointer to next block    */
    size_t bsize,               /* Block size = header + payload */
           padd;
    long data[1];               /* Payload */
} Block;

static Block *head_list = NULL,
             *tail_list = NULL,
             *head_free = NULL;
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
            tail_list -> next     = p;
            p -> prev             = tail_list;
            tail_list             = p;
        }
        else {
            p -> prev             = NULL;
            head_list = tail_list = p;
        }

        if ( !head_free )
            head_free = p;

        p -> bsize = bsize;
        p -> next  = NULL;

        bp = p;
    }

    return bp;
}

/*
 * Initialize: returns false on error, true on success.
 */
bool 
mm_init(void){

    head_list = tail_list = head_free = NULL;

    bsize_of_minblock = align_size (1);

    return true;
}


static Block*
get_next_block ( Block * bp ){
    return (Block*)((char*)bp + (bp -> bsize & ~1ull));
}

static void*
find_fit(size_t bsize){
    Block * bp, *start;
    if ( head_free )
        start = head_free;
    else
        start = tail_list;
    for ( bp = start; bp; bp = bp -> next ){
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

        if ( bn -> next )
            bn -> next -> prev = bn;

        if ( tail_list == bp )
            tail_list = bn;
        if ( head_free == bp )
            head_free = bn;
    }

    bp -> bsize |=1;

    if ( bp == head_free )
        head_free = NULL;
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

    //mm_checkheap (__LINE__);

    if (size){

        size_t bsize = align_size ( size );

        bp = find_fit ( bsize );

        if ( !bp )
            bp = extend_heap ( bsize );

        if ( bp )
            alloc_block ( bp, bsize );

        dbg_printf("\nmalloc: %p  bp %p size=%ld bsize=%ld\n",&bp->data[0],bp,size,bsize);
    }

    mm_checkheap (__LINE__);

    //{ Block * p; for ( p = head_list; p; p = p -> next ) if ( p == bp ) break; if ( p != bp ){ printf("bp: %p not found in list!\n",bp); abort(); } }
    return bp ? &bp -> data[0] : NULL;
} 

/*
 * free
 */
void 
free(void* ptr){
    bool prev_free, next_free;

    Block * bp = get_block_ptr ( ptr );

    dbg_printf("\nfree  : %p  bp %p\n",ptr,bp);

    prev_free = (bp -> prev && !(bp -> prev -> bsize & 1 )) ? true : false;
    next_free = (bp -> next && !(bp -> next -> bsize & 1 )) ? true : false;

    bp -> bsize &= ~1ull;

    if (  prev_free && !next_free ){
        if ( bp == tail_list )
            tail_list = bp -> prev;
        bp -> prev -> bsize += bp -> bsize;
        bp -> prev -> next   = bp -> next;
        if ( bp -> next )
            bp -> next -> prev = bp -> prev;

        if ( head_free ){
            if ( head_free > bp -> prev )
                head_free = bp -> prev;
        }
        else 
            head_free = bp -> prev;
    }
    else
    if ( !prev_free && next_free  ){
        if ( bp -> next == tail_list )
            tail_list = bp;
        bp -> bsize += bp -> next -> bsize;
        if ( bp -> next -> next )
            bp -> next -> next -> prev = bp;
        bp -> next   = bp -> next -> next;

        if ( head_free ){
            if ( head_free > bp )
                head_free = bp;
        }
        else 
            head_free = bp;
    }
    else
    if (  prev_free && next_free  ){
        if ( bp -> next == tail_list )
            tail_list = bp -> prev;
        bp -> prev -> bsize += bp -> bsize + bp -> next -> bsize;
        bp -> prev -> next = bp -> next -> next;
        if ( bp -> next -> next )
            bp -> next -> next -> prev = bp -> prev;

        if ( head_free ){
            if ( head_free > bp -> prev )
                head_free = bp -> prev;
        }
        else 
            head_free = bp -> prev;
    }
    else 
    if ( !prev_free && !next_free ){
        if ( head_free ){
            if ( head_free > bp )
                head_free = bp;
        }
        else 
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
    if (bp)
    printf("p %p - bp %p: %s {prev: %p, next: %p} bsize=%llu\n",&bp->data[0],bp,(bp -> bsize & 1) ? "A":"F", bp -> prev, bp -> next, bp -> bsize & ~1ull);
}

static void
printlist(void){
    for ( Block * pb = head_list; pb; pb = pb -> next ) printblock(pb);
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
    #ifdef DEBUG
    Block * pb; 
    #endif
    if ( head_list && head_list -> prev ){
            #ifdef DEBUG
            printf("%d bad head =%p\n",lineno,head_list); for ( pb = head_list; pb; pb = pb -> next ) printblock(pb); abort();
            #endif
            return false;
    }
    if ( tail_list && (tail_list -> next || (tail_list -> prev && tail_list -> prev < (Block*)0x10000) ) ){
            #ifdef DEBUG
            printf("%d bad tail =%p\n",lineno,tail_list); for ( pb = head_list; pb; pb = pb -> next ) printblock(pb); abort();
            #endif
            return false;
    }

    #ifdef DEBUG
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

    { pb = tail_list; int k = 500; while ( pb && pb -> prev && k--) pb = pb -> prev; printf("line: %d\n",lineno);for ( ;pb; pb = pb -> next ) printblock(pb); }
    #endif

    return true;
}

