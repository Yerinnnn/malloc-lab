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
#define MIN_BLOCK_SIZE 24
#define CHUNKSIZE (1<<12)  // Extend heap by this amount (bytes)
#define LISTLIMIT 20

#define MAX(x, y) ((x) > (y)? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))  // header/footer에 저장될 값 생성 (크기 + 할당 여부 비트)

#define GET(p) (*(unsigned int *)(p))  // 주소 p의 값을 가져오기 (4바이트씩 읽기 위해 unsigned int*로 변환)
#define PUT(p, val) (*(unsigned int *)(p) = (val))  // 주소 p의 값을 저장하기

#define GET_SIZE(p) (GET(p) & ~0x7)  // header/footer에서 size 추출 (하위 3비트 제외하고 사이즈만)
#define GET_ALLOC(p) (GET(p) & 0x1)  // header/footer에서 alloc bit 추출 (하위 1비트: 0이면 free, 1이면 할당됨)

#define HDRP(bp) ((char *)(bp) - WSIZE)  // 블록 포인터(bp)에서 헤더 주소를 계산 (bp는 payload 시작 주소)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)  // 블록 포인터에서 푸터 주소

#define PRED(bp) (*(void **)(bp))  // 연결 리스트의 이전 주소
// (char *) : bp를 바이트 단위로 주소 연산하기 위해 char*로 변환
//            int*나 void*는 주소 연산 시 4바이트 단위(32비트 기준)로 움직이기 때문
//            char*는 1바이트 단위니까 정확한 주소 계산이 가능
#define SUCC(bp) (*(void **)((char *)(bp) + WSIZE))  // 연결 리스트의 다음 주소 (bp에서 4바이트 떨어진 주소 계산)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))  // 힙의 다음 블록 포인터 (정확한 오프셋 계산을 위해 1바이트씩 증가하는 char*로 형변환)
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))  // 힙의 이전 블록 포인터

static char *heap_listp;  // 힙의 시작 주소를 저장하는 포인터
static void *segregation_list[LISTLIMIT];

// forward declaration
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void insert_node(void *bp);
static void remove_node(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/*
 * insert_node - 가용 연결 리스트에 블록 삽입
 */
static void insert_node(void *bp) {
    int list_idx = 0;  // 사용할 리스트 인덱스
    void *curr;  // 리스트를 탐색하며 현재 비교 중인 노드
    void *prev = NULL;  // curr 직전 노드 (삽입 위치)

    size_t size = GET_SIZE(HDRP(bp));  // 삽입할 블록의 크기

    // 블록 크기에 따라 적절한 리스트 인덱스를 선택
    // 마지막 리스트 전까지, 블록 크기가 줄어들 여지가 있을 때까지 size를 절반으로 줄이며 적절한 리스트 인덱스 탐색
    // size가 1 이하가 되면 그 이상 분류할 필요가 없음
    while ((list_idx < LISTLIMIT - 1) && (size > 1)) {
        // 2로 나누면서 크기 구간 좁혀가기
        // 크기를 절반으로 줄여가면서, 얼마나 큰 크기인지를 판단 -> 작은 블록은 낮은 인덱스의 리스트로, 큰 블록은 높은 인덱스로 보냄

        // size = 128;
        // list_idx = 0;

        // 128 > 1 → list_idx = 1, size = 64
        // 64 > 1 → list_idx = 2, size = 32
        // 32 > 1 → list_idx = 3, size = 16
        // ...

        // → 크기에 따라 list_idx가 점점 증가
        size >>= 1;
        list_idx++;
    }
    
    curr = segregation_list[list_idx];
    
    // curr이 NULL이 아니고, 현재 curr의 크기가 bp보다 작으면 계속 이동
    while ((curr != NULL) && (size >= GET_SIZE(HDRP(curr)))) {
        prev = curr;        // 이전 노드 기억
        curr = SUCC(curr);  // 다음 노드로 이동
    }

    // curr이 NULL이 아닐 때,
    // 중간 또는 head에 삽입
    if (curr != NULL) {
        // prev이 NULL이 아닐 때
        if (prev != NULL) {
            // 중간 삽입
            SUCC(bp) = curr;
            PRED(bp) = prev;
            PRED(curr) = bp;
            SUCC(prev) = bp;
        } else {
            // head에 삽입
            SUCC(bp) = curr;
            PRED(bp) = NULL;
            PRED(curr) = bp;
            segregation_list[list_idx] = bp;
        }
    }
    // curr이 NULL일 때,
    // 리스트의 끝에 삽입
    else {
        if (prev != NULL) {
            // 마지막 노드 뒤에 삽입
            SUCC(bp) = NULL;
            PRED(bp) = prev;
            SUCC(prev) = bp;
        }
        // 아무것도 없어서 list에 내가 처음 넣을 때
        else {
            // 리스트에 아무 것도 없을 경우 (첫 삽입)
            SUCC(bp) = NULL;
            PRED(bp) = NULL;
            segregation_list[list_idx] = bp;
        }
    }
    return;
}

/*
 * extend_heap - 힙을 words 개수만큼 확장하고 새 가용 블록 생성
 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    // 정렬을 맞추기 위해 words가 홀수면 +1
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;

    if (size < MIN_BLOCK_SIZE)
        size = MIN_BLOCK_SIZE;

    // mem_sbrk(size): size만큼 힙 공간을 추가 요구
    if ((long) (bp = mem_sbrk(size)) == -1)
        return NULL;

    // 새 블록의 헤더/푸터, 새로운 epilogue 블록 세팅
    PUT (HDRP(bp), PACK(size, 0));  // 새 가용 블록의 헤더
    PUT (FTRP(bp), PACK(size, 0));  // 새 가용 블록의 푸터
    PUT (HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 새 에필로그 헤더

    // 연결 리스트 포인터 초기화
    PRED(bp) = NULL;
    SUCC(bp) = NULL;

    // 이전 블록과 병합 시도
    return coalesce(bp);
}

/* 
 * mm_init - 힙 초기화
 */
int mm_init(void)
{
    int list;

    for (list = 0; list < LISTLIMIT; list++) {
        segregation_list[list] = NULL;     // segregation_list를 NULL로 초기화
    }
    
    // 4개의 워드 공간을 요청: 패딩 + 프롤로그 헤더 + 프롤로그 푸터 + 에필로그
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    // 힙 세팅: padding, prologue, epilogue
    PUT(heap_listp, 0);                                // 패딩
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));     // 프롤로그 헤더
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));     // 프롤로그 푸터
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));         // 에필로그 헤더
    heap_listp += (2 * WSIZE);                         // bp는 payload 시작점으로 옮김

    // 힙에 초기 가용 블록 생성 (힙에 최소한의 가용 공간이 있어야 malloc 요청을 처리할 수 있기 때문에)
    // CHUNKSIZE = 1 << 12 = 4096바이트
    // WSIZE = 4바이트 (word size)
    // CHUNKSIZE / WSIZE = 1024 word → 총 4096바이트만큼 힙을 늘림
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    if (extend_heap(4) == NULL) return -1;  // 현호가 추가해준 코드

    return 0;
}

/*
 * remove_node - 가용 연결 리스트에서 블록 제거
 */
static void remove_node(void *bp) {
    int list_idx = 0;
    size_t size = GET_SIZE(HDRP(bp));

    // bp 크기에 따라 해당되는 리스트 인덱스를 구함
    while ((list_idx < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        list_idx++;
    }

    if (SUCC(bp) != NULL) {  // bp의 다음 노드가 존재할 경우
        if (PRED(bp) != NULL) {  // 이전 노드가 존재한다면,
            // 중간에 있는 노드를 제거하는 경우
            PRED(SUCC(bp)) = PRED(bp);
            SUCC(PRED(bp)) = SUCC(bp);
        } else {
            // head를 제거하는 경우
            PRED(SUCC(bp)) = NULL;
            segregation_list[list_idx] = SUCC(bp);
        }
    } else {  // SUCC 블록이 NULL일 경우,
        // 마지막 노드 제거
        if (PRED(bp) != NULL) {
            // 마지막 노드지만 앞에 노드가 있는 경우
            SUCC(PRED(bp)) = NULL;
        } else {
            // 리스트에 bp 하나만 있을 경우
            segregation_list[list_idx] = NULL;
        }
    }

    return;
}

/*
 * coalesce - 인접한 가용 블록들과 병합
 */
static void *coalesce(void *bp) {
    // 가용 리스트와 관계 없이 물리적으로 인접한 블록만 병합 가능
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));   // 이전 블록의 할당 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));   // 다음 블록의 할당 여부
    size_t size = GET_SIZE(HDRP(bp));                     // 현재 블록 크기    
    
    // Case 1: 이전, 다음 모두 할당 상태
    if (prev_alloc && next_alloc) {
        insert_node(bp);  // 현재 블록만 가용 리스트에 삽입
        return bp;
    }

    // Case 2: 다음 블록만 가용
    else if (prev_alloc && !next_alloc) {
        remove_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));         // 다음 블록과 병합
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));  // 이미 병합이 되었으니 bp 사용 가능
    }

    // Case 3: 이전 블록만 가용
    else if (!prev_alloc && next_alloc) {
        remove_node(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));       // 이전 블록과 병합
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);                          // 병합된 블록의 시작 주소로 이동
    }

    // Case 4: 이전, 다음 모두 가용
    else {
        remove_node(PREV_BLKP(bp));
        remove_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);                          // 병합된 블록의 시작 주소로 이동
    }

    insert_node(bp);
    return bp;
}

/*
 * find_fit - first-fit 방식으로 가용 리스트에서 적절한 블록을 찾음
 */
void *find_fit(size_t asize) {
    // implicit에서는 전체 heap 리스트를 순회했지만,
    // explicit에서는 가용 리스트만 순회해야 함

    /*
    first fit
    */
    void *bp;

    int list_idx = 0;
    size_t searchSize = asize;

    // LISTLIMIT까지 순회
    while (list_idx < LISTLIMIT) {
        // 현재 리스트에 적절한 크기의 블록이 있거나 마지막 리스트에 도달했을 경우
        if ((list_idx == LISTLIMIT - 1) || ((searchSize <= 1) && (segregation_list[list_idx] != NULL))) {
            bp = segregation_list[list_idx];

            // 현재 리스트에서 첫 번째로 맞는 블록 찾기 (first-fit)
            while ((bp != NULL) && (asize > GET_SIZE(HDRP(bp)))) {
                bp = SUCC(bp);
            }

            // 조건에 맞는 블록을 찾았을 경우 즉시 반환
            if (bp != NULL){
                return bp;
            }
        }

        // 다음 리스트로 넘어가기 위해 기준 크기 절반으로 줄이기
        searchSize >>= 1;
        list_idx++;
    }

    return NULL;  // 적절한 블록을 찾지 못함

    /*
    best fit
    */
    // void *bp = NULL;
    // void *best_fit = NULL;
    // size_t best_size = (size_t)-1;

    // int list = 0;
    // size_t searchSize = asize;

    // while (list < LISTLIMIT) {
    //     if (segregation_list[list] != NULL) {
    //         bp = segregation_list[list];
    //         while (bp != NULL) {
    //             size_t bsize = GET_SIZE(HDRP(bp));
    //             if (bsize >= asize && (bsize - asize) < best_size) {
    //                 best_size = bsize - asize;
    //                 best_fit = bp;
    //                 if (best_size == 0) break; // perfect fit
    //             }
    //             bp = SUCC(bp);
    //         }
    //         if (best_fit != NULL) break;
    //     }
    //     searchSize >>= 1;
    //     list++;
    // }

    // return best_fit;
}

/*
 * place - 가용 블록에 메모리를 할당하고, 필요시 분할하여 가용 리스트에 나머지를 삽입
 */
void place(void *bp, size_t asize) {
    // 현재 가용 블록의 전체 크기를 csize에 저장 (헤더에 들어있음)
    size_t csize = GET_SIZE(HDRP(bp));

    // 할당이 결정된 가용 블록은 가용 리스트에서 제거
    // bp는 find_fit() 함수에서 malloc 요청에 사용할 가용 블록으로 선택된 블록
    // → 그러니까 place() 함수가 실행될 때는 이미 malloc 요청에 사용할 블록으로 결정된 상태
    remove_node(bp);

    // csize와 요청한 크기 asize를 비교
    // 만약 (csize - asize) >= 최소 분할 크기 (24바이트) 이면:
    if ((csize - asize) >= MIN_BLOCK_SIZE) {
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

        // 새로운 가용 블록의 연결 리스트 포인터 초기화
        PRED(next_bp) = NULL;
        SUCC(next_bp) = NULL;

        insert_node(next_bp);
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
void *mm_malloc(size_t size) {
    // mm_malloc 시작 부분에 추가
    // printf("malloc called with size: %zu\n", size);
    size_t asize;  // 조정된 블록 크기
    size_t extendsize;  // 힙 확장 필요 시 크기
    char *bp;

    // 0 크기 요청 무시
    if (size == 0) return NULL;

    // 최소 블록 크기 맞춰 정렬 (헤더 + 푸터 포함해서 최소 24)
    if (size <= DSIZE) {
        asize = MIN_BLOCK_SIZE;
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
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - 메모리 해제
 */
void mm_free(void *ptr) {
    if (ptr == NULL) return;

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

    // ptr이 NULL이면 재할당할 기존 메모리가 없다는 것이므로, malloc과 동일
    if (ptr == NULL) {
        return mm_malloc(size);
    }

    // size가 0이면 free와 동일 (기존 메모리 해제하고, 아무 것도 안 받겠다는 의미)
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }
    
    newptr = mm_malloc(size);  // 새 메모리 블록 할당
    if (newptr == NULL)
      return NULL;

    // 복사할 크기는 원래 블록의 사이즈 (헤더/푸터 크기 제외)
    copySize = GET_SIZE(HDRP(oldptr)) - DSIZE;

    // 요청된 크기보다 원래 크기가 크면 잘라서 복사 (사용자가 요청한 만큼만 복사)
    if (size < copySize)
      copySize = size;

    memcpy(newptr, oldptr, copySize);  // 데이터 복사 (payload만 복사됨)
    mm_free(oldptr);                   // 기존 블록 반환
    return newptr;
}
