/*
 * mm.c
 *
 * Name: Malav Patel
 *
 * INSERT: HIGH LEVEL DESCRIPTION OF SOL
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
//#define DEBUG 2

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

static void printFree(void);
static void printHeap(void);
static size_t get_free_index ( size_t bsize );

typedef struct free_list {
    void * bp;
    struct free_list * next;
} free_list;

static char *heap_listp = 0;

enum {
    BSZ_32   ,
    BSZ_64   ,
    BSZ_128  ,
    BSZ_256  ,
    BSZ_512  ,
    BSZ_1024 ,
    BSZ_2048 ,
    BSZ_4096 ,
    BSZ_8192 ,
    BSZ_LEN
};

static size_t * free_head[BSZ_LEN];

static size_t total = 0;

/* What is the correct alignment? */
#define ALIGNMENT 16

static size_t WSIZE = 8;

static size_t DSIZE = 16;

static size_t CHUNKSIZE  = (1<<12); 

static size_t MAX(size_t x, size_t y) {
    if (x > y){
        return x;
    }
    else{
        return y;
    }
}

static size_t PACK(size_t size, size_t alloc){
    return (size|alloc);
}
static size_t GET(void* p){
    return (*(size_t*)(p));
}
static size_t PUT(void* p, size_t val) {
    return (*(size_t *)(p) = (val));
}

static size_t GET_SIZE(size_t* p) {
    return (GET(p) & ~0x7);
}

static size_t GET_ALLOC(size_t* p){
    return (GET(p) & 0x1);
}

static void* HDRP(void *bp){
    return ((char *)(bp) - WSIZE);
}

static void* FTRP(void* bp){
    return ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE);
}

static void* NEXT_BLKP(void* bp){
    return ((char *)(bp) + GET_SIZE(((bp) - WSIZE)));
}

static void* PREV_BLKP(void* bp){
    return ((char *)(bp) - GET_SIZE(((bp) - DSIZE)));
}



/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x)
{
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

static void unlink2 ( size_t * bp, size_t ** head ){
    if ( bp[0] )
        ((size_t*)bp[0])[1] = bp[1];
    if ( bp[1] )
        ((size_t*)bp[1])[0] = bp[0];

    if ( *head == bp )
        *head = (size_t*)bp[1];
}

static void linkh ( size_t * bp, size_t ** head ){
    bp[0] = 0;
    bp[1] = (size_t)(*head);
    if ( *head )
        (*head)[0] = (size_t)bp;
    *head = bp;
}

static void *coalesce(void *bp) 
{
    size_t*prev = PREV_BLKP(bp),
          *next = NEXT_BLKP(bp);
    size_t prev_alloc = GET_ALLOC(FTRP(prev));
    size_t next_alloc = GET_ALLOC(HDRP(next));
    size_t size = GET_SIZE(HDRP(bp)), old_size, nxt_size;
    size_t * p = (size_t*)bp;
    size_t old_index, index, nxt_index;

    if (prev_alloc && next_alloc) {            /* Case 1 */
        index = get_free_index(size);
        p[0] = 0;
        p[1] = 0;
        if ( free_head[index] ){
            p[1] = (size_t)free_head[index];
            free_head[index][0] = (size_t)p;
        }
        free_head[index] = p;

        return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2  A  A->F F */
        old_size  = GET_SIZE(HDRP(NEXT_BLKP(bp)));
        old_index = get_free_index ( old_size );

        size += old_size;
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));

        index = get_free_index ( size );

        p[0] = next[0];
        p[1] = next[1];

        if ( p[0] )
            ((size_t*)p[0])[1] = (size_t)p;
        if ( p[1] )
            ((size_t*)p[1])[0] = (size_t)p;

        if ( next == free_head[index] )
            free_head[index] = p;

        if ( old_index != index ){
            unlink2 ( next, free_head + old_index );
            linkh   ( p   , free_head +     index );
        } 

    }

    else if (!prev_alloc && next_alloc) {      /* Case 3  F A->F A */
        old_size  = GET_SIZE(HDRP(PREV_BLKP(bp)));
        old_index = get_free_index ( old_size ); 

        size += old_size;
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);

        index = get_free_index ( size );

        if ( old_index != index ){
            unlink2 ( bp, free_head + old_index );
            linkh   ( bp, free_head +     index );
        }
    }

    else {                                     /* Case 4 */
        old_size  = GET_SIZE(HDRP(PREV_BLKP(bp)));
        nxt_size  = GET_SIZE(FTRP(NEXT_BLKP(bp)));
        old_index = get_free_index ( old_size );
        nxt_index = get_free_index ( nxt_size );

        size += old_size + nxt_size;
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);

        index = get_free_index ( size );

        unlink2 ( next, free_head + nxt_index );

        if ( old_index != index ){
            unlink2 ( bp, free_head + old_index );
            linkh   ( bp, free_head +     index );
        }
    }
    return bp;
}

static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size;
  
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 

    if ((long)(bp = mem_sbrk(size)) == -1)  
        return NULL;                                   

    total += size;
  
    PUT(HDRP(bp), PACK(size, 0));         
    PUT(FTRP(bp), PACK(size, 0));        
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); 

    return coalesce ( bp );
}

/*
 * Initialize: returns false on error, true on success.
 */
bool mm_init(void)
{
    memset( free_head, 0, sizeof(free_head) );

    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return false;
    total += 4*WSIZE;
    PUT(heap_listp, 0);
    /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2*WSIZE);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL){
        mm_checkheap(0);
        return false;
    }
    mm_checkheap(0);

    return true;
}

static unsigned long pof2 (unsigned long v)
{
    v--;
    v |= v >> 1;
    v |= v >> 2;
    v |= v >> 4;
    v |= v >> 8;
    v |= v >> 16;
    v++;
    return v;
}

static size_t get_free_index ( size_t bsize ){
    if ( bsize <=   32 ) return BSZ_32;
    if ( bsize <=   64 ) return BSZ_64;
    if ( bsize <=  128 ) return BSZ_128;
    if ( bsize <=  256 ) return BSZ_256;
    if ( bsize <=  512 ) return BSZ_512;
    if ( bsize <= 1024 ) return BSZ_1024;
    if ( bsize <= 2048 ) return BSZ_2048;
    if ( bsize <= 4096 ) return BSZ_4096;
    return BSZ_8192;
}

static void *find_fit(size_t asize)

{
    size_t index = get_free_index (asize);
#if 0
    void *bp;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
#else
    size_t *bp;
    for ( int i = index; i < BSZ_LEN; ++i ){
        for (bp = free_head[i]; bp ; bp = (size_t*)bp[1] ){
            if (asize <= GET_SIZE(HDRP(bp))) 
                return bp;
        }
    }
#endif
    return NULL; /* No fit */
}
 

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));   
    size_t * p = (size_t*)bp; 

    size_t index, old_index; 

    if ((csize - asize) >= (2*DSIZE)) { 
        old_index = get_free_index ( csize );

        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));

        index = get_free_index ( csize-asize );
        size_t * next = (size_t*)bp;
        next[0] = p[0];
        next[1] = p[1];
        if ( p[0] )
            ((size_t*)p[0])[1] = (size_t)next;
        if ( p[1] )
            ((size_t*)p[1])[0] = (size_t)next;

        if ( p == free_head[old_index] )
            free_head[old_index] = next;

        if ( old_index != index ){
            unlink2 ( next, free_head + old_index );
            linkh   ( next, free_head +     index );
        }
    }
    else { 
        index = get_free_index ( csize );
        if ( p[0] )
            ((size_t*)p[0])[1] = p[1];
        if ( p[1] )
            ((size_t*)p[1])[0] = p[0];
        if ( p == free_head[index] )
            free_head[index] = (size_t*)p[1];

        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
/*
 * malloc
 */
void* malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;      


    /* $end mmmalloc */
    if (heap_listp == 0){
        mm_init();
    }
    /* $begin mmmalloc */
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)                                       
        asize = 2*DSIZE;                       
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {  
        place(bp, asize);                 
        dbg_printf( "malloc: %p  %lu\n",bp,size);
        #if defined DEBUG && DEBUG > 1
        printHeap(); printFree(); printf("+++++++++++++++++++++++++++++\n\n");
        #endif
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);              
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  
        return NULL;                                
    place(bp, asize);                                

    dbg_printf( "malloc: %p  %lu\n",bp,size);

    #if defined DEBUG && DEBUG > 1
    printHeap(); printFree(); printf("+++++++++++++++++++++++++++++\n\n");
    #endif

    mm_checkheap(0);
    return bp;
} 

/*
 * free
 */
void free(void* ptr)
{

    dbg_printf( "free  : %p\n",ptr);
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    coalesce ( ptr );
    #if defined DEBUG && DEBUG > 1
    printHeap(); printFree(); printf("-----------------------------\n\n");
    #endif

    mm_checkheap(0);
}

/*
 * realloc
 */
void* realloc(void* oldptr, size_t size)
{
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        free(oldptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(oldptr == NULL) {
        return malloc(size);
    }

    newptr = malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return 0;
    }

    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(oldptr));
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
void* calloc(size_t nmemb, size_t size)
{
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
static bool in_heap(const void* p)
{
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Returns whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void* p)
{
    size_t ip = (size_t) p;
    return align(ip) == ip;
}

void printFree(void){
    size_t * p;
    for ( int i = 0; i < BSZ_LEN; ++i  ){
    for ( p = free_head[i]; p; p = (size_t*)p[1] ){
        size_t hsize  = GET_SIZE(HDRP(p));
        size_t halloc = GET_ALLOC(HDRP(p));  
        printf("free %4d: bp %p  prev %p  next %p  size %ld  %s\n",32<<i,p,(size_t*)(p[0]),(size_t*)(p[1]),hsize,halloc?"A":"F");
    }
    }

}
void printHeap(void){
    void * bp;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        size_t hsize  = GET_SIZE(HDRP(bp));
        size_t halloc = GET_ALLOC(HDRP(bp));  
        printf("heap: bp %p  size %ld  %s\n",bp,hsize,halloc?"A":"F");
    }

}

static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    mm_checkheap(0);
    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  

    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%ld:%c] footer: [%ld:%c]\n", bp, 
           hsize, (halloc ? 'a' : 'f'), 
           fsize, (falloc ? 'a' : 'f')); 
}

static void checkblock(void *bp) 
{
    if ((size_t)bp % 8)
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
}

static void prn(void){
    printHeap();
    printFree();
}

/*
 * mm_checkheap
 */
bool mm_checkheap(int lineno)
{
#ifdef DEBUG
    /* Write code to check heap invariants here */
    /* IMPLEMENT THIS */
    {
    char *bp = heap_listp;

    if (lineno)
        printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");
    checkblock(heap_listp);

    size_t total_size = 0, free_size_total = 0;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (lineno) 
            printblock(bp);
        checkblock(bp);
        total_size += GET_SIZE(HDRP(bp));
        if ( !GET_ALLOC(HDRP(bp)) )
            free_size_total += GET_SIZE(HDRP(bp));
    }


    if (lineno)
        printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");

    //size_t free_size = 0;
    {
        size_t *bp, *p;
        for ( int i = 0; i < BSZ_LEN; ++i ){
            for (bp = free_head[i]; bp ; bp = (size_t*)bp[1] ){
                if (GET_ALLOC(HDRP(bp))) {
                    printf("Bad Free Block!\n");
                    abort();
                }
                //free_size = GET_SIZE(HDRP(bp));
        
                for ( p = (size_t*)heap_listp; GET_SIZE(HDRP(p)) > 0; p = NEXT_BLKP(p)) {
                    if ( bp == p )
                        break;
                }
                if ( bp != p ){
                    prn();
                    printf("Bad Free List!\n");
                    abort();
                }

            }
        }
    }

   //if( free_size != free_size_total ){
   //    printf("free_size = %ld free_size_total=%ld total=%ld total_size=%ld\n",free_size,free_size_total,total, total_size);
   //     abort();
   //}
    }
#endif
    return true;
}
