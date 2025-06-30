/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
// (size + 7) : size가 8의 배수가 아니면 8의 배수로 올림
// & ~0x7 : 마지막 3비트를 0으로 만들어서 8의 배수 정렬
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

// size_t : 음수가 필요 없고, 최대한 큰 범위를 표현할 때 사용
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4  // Word and header/footer size (bytes)
#define DSIZE 8  // Double word size (bytes)
#define CHUNKSIZE (1<<12)  // Extend heap by this amount (bytes)

#define MAX(x, y) ((x) > (y)? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))  // header/footer에 저장될 값 생성 (크기 + 할당 여부 비트)

#define GET(p) (*(unsigned int *)(p))  // 주소 p의 값을 가져오기
#define PUT(p, val) (*(unsigned int *)(p) = (val))  // 주소 p의 값을 저장하기

#define GET_SIZE(p) (GET(p) & ~0x7)  // header/footer에서 size 추출 (하위 3비트 제외하고 사이즈만)
#define GET_ALLOC(p) (GET(p) & 0x1)  // header/footer에서 alloc bit 추출 (하위 1비트: 0이면 free, 1이면 할당됨)

#define HDRP(bp) ((char *)(bp) - WSIZE)  // 블록 포인터(bp)에서 헤더 주소를 계산 (bp는 payload 시작 주소)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)  // 블록 포인터에서 푸터 주소

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))  // 다음 블록 포인터
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))  // 이전 블록 포인터

static char *heap_listp;  // 힙의 시작 주소를 저장하는 포인터


static void *coalesce(void *bp);


/*
 * extend_heap - 힙을 words 개수만큼 확장하고 새 가용 블록 생성
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // 정렬을 맞추기 위해 words가 홀수면 +1
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;

    // mem_sbrk(size): size만큼 힙 공간을 추가 요청
    if ((long) (bp = mem_sbrk(size)) == -1)
        return NULL;

    // 새 블록의 헤더/푸터, 새로운 epilogue 블록 세팅
    PUT (HDRP (bp), PACK(size, 0));  // 새 가용 블록의 헤더
    PUT (FTRP (bp), PACK(size, 0)) ;  // 새 가용 블록의 푸터
    PUT (HDRP (NEXT_BLKP(bp)), PACK(0, 1)); // 새 에필로그 헤더

    // 이전 블록과 병합 시도
    return coalesce (bp) ;
}

/* 
 * mm_init - 힙 초기화
 */
int mm_init(void)
{
    // 4개의 워드 공간을 요청: 패딩 + 프롤로그 헤더 + 프롤로그 푸터 + 에필로그
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    // 힙 세팅: padding, prologue, epilogue
    PUT(heap_listp, 0);                                // 패딩
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));     // 프롤로그 헤더
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));     // 프롤로그 푸터
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));         // 에필로그 헤더
    heap_listp += (2 * WSIZE);                         // bp는 payload 시작점으로 옮김

    // 힙에 초기 가용 블록 생성
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

    return 0;
}

/*
 * coalesce - 인접한 가용 블록들과 병합
 */
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));   // 이전 블록의 할당 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));   // 다음 블록의 할당 여부
    size_t size = GET_SIZE(HDRP(bp));                     // 현재 블록 크기
    
    /// Case 1: 이전, 다음 모두 할당 상태
    if (prev_alloc && next_alloc) {
        return bp;
    }

    // Case 2: 다음 블록만 가용
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));         // 다음 블록과 병합
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));  // 이미 병합이 되었으니 bp 사용 가능
    }

    // Case 3: 이전 블록만 가용
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));       // 이전 블록과 병합
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);                          // 병합된 블록의 시작 주소로 이동
    }

    // Case 4: 이전, 다음 모두 가용
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);                          // 병합된 블록의 시작 주소로 이동
    }
    return bp;
}

void *find_fit(size_t asize) {
    void *bp = heap_listp;

    while (GET_SIZE(HDRP(bp)) > 0) {
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize)
            return bp;
        bp = NEXT_BLKP(bp);
    }

    return NULL;
}

void place(void *bp, size_t asize) {
    // 현재 가용 블록의 전체 크기를 csize에 저장 (헤더에 들어있음)
    size_t csize = GET_SIZE(HDRP(bp));

    // csize와 요청한 크기 asize를 비교

    // 만약 (csize - asize) >= 최소 분할 크기 (16바이트) 이면:
    if ((csize - asize) >= 2 * DSIZE) {
        // 앞쪽 asize만큼을 할당된 블록으로 만들고,
        // 해당 영역의 헤더와 푸터에 (asize, alloc=1) 정보를 기록
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        // 남은 공간 (csize - asize)은 새 가용 블록으로 만들고,
        void *next_bp = NEXT_BLKP(bp);
        // 다음 블록의 시작 주소를 계산하고,
        // 그 위치에 (csize - asize, alloc=0) 헤더와 푸터를 기록
        PUT(HDRP(next_bp), PACK(csize - asize, 0));
        PUT(FTRP(next_bp), PACK(csize - asize, 0));
    }
    // 그렇지 않으면 (남은 공간이 너무 작으면): 
    else {
        // 전체 블록을 통째로 할당함
        // 헤더와 푸터에 (csize, alloc=1) 정보를 기록함
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* 
 * mm_malloc - 힙에서 메모리를 size만큼 할당
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;  // 조정된 블록 크기
    size_t extendsize;  // 힙 확장 필요 시 크기
    char *bp;

    // 0 크기 요청 무시
    if (size == 0) return NULL;

    // 최소 블록 크기 맞춰 정렬 (헤더 + 푸터 포함해서 최소 16)
    if (size <= DSIZE) {
        asize = 2 * DSIZE;
    }
    else {
        asize = ALIGN(size + DSIZE);  // DSIZE: 헤더+푸터 포함 크기
    }
    
    // find_fit에서 가용 블록 찾기
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    // 가용 블록이 없으면 힙 확장
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - 메모리 해제
 */
void mm_free(void *ptr) {
    size_t size = GET_SIZE(HDRP(ptr));      // 블록 크기

    PUT(HDRP(ptr), PACK(size, 0));          // 헤더: free 표시
    PUT(FTRP(ptr), PACK(size, 0));          // 푸터: free 표시
    coalesce(ptr); 
}

/*
 * mm_realloc - 크기를 조절한 새 블록을 할당하고 기존 데이터 복사
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);  // 새 메모리 블록 할당
    if (newptr == NULL)
      return NULL;

    // 복사할 크기는 원래 블록의 사이즈
    copySize = GET_SIZE(HDRP(oldptr));

    // 요청된 크기보다 원래 크기가 크면 잘라서 복사
    if (size < copySize)
      copySize = size;

    memcpy(newptr, oldptr, copySize);  // 데이터 복사
    mm_free(oldptr);                   // 기존 블록 반환
    return newptr;
}
