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
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE 4 // 워드 크기 4 바이트
#define DSIZE 8 // 더블 워드 크기 8 바이트
#define CHUNKSIZE (1 << 12) // 힙을 확장할 때 기본 크기 4096 바이트

#define MAX(x, y) ((x) > (y) ? (x) : (y)) // 걍 뭐 둘 중에 더 큰거 반환

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc)) // 블록 header/footer에 저장할 값 구성 (크기 + 할당 비트)

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p)) // 포인터 위치의 4바이트 값을 읽음
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 포인터 위치에 값을 씀? 덮어쓴다?

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7) // 전체 값에서 하위 3비트(할당 여부 플래그)를 제거한 순수한 블록 크기
#define GET_ALLOC(p) (GET(p) & 0x1) // 하위 비트가 1이면 할당된다. 0 이면 할당 안함

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE) // 블록 포인터로부터 헤더 위치
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 블록 포인터로부터 푸터 위치

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Global variables */
static char *heap_listp = 0; // 힙의 시작을 가리키는 포인터
static char *rover = 0;

// 인접한 블록이 비어있다면, 하나의 큰 블록으로 합쳐서 외부 단편화를 줄인다.
static void *coalesce(void *bp) {
    // 현재 블록을 기준으로 이전/다음 브롥이 할당 중인지 확인한다.
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록의 크기

    // 앞/뒤 모두 할당되어 있음
    // 아무것도 안함
    if (prev_alloc && next_alloc) {
        return bp;
    // 앞은 할당, 뒤는 비어있음
    // 다음 블록이 비어있으므로 병합 가능함, 현재 블록과 다음 블록의 크기를 합쳐서 새 블록을 구성
    // 새 블록의 헤더/풋터를 모두 size, alloc=0으로 설정
    } else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    // 앞은 비어있음, 뒤는 할당
    // 이전 블록이 비어있으므로 병합 가능함, 이전 블록과 현재 블록의 크기를 합침
    // 헤더는 이전 블록의 위치에, 풋터는 현재 블록의 끝에 병합 후 반환 포인터 bp를 이전 블록으로 갱신
    } else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    // 앞/뒤 모두 빈 블록
    // 총 3개의 블록을 하나로 병합
    // 이전 + 현재 + 다음 블록
    // 헤더는 이전 블록의 헤더에, 풋터는 다음 블록의 풋터에
    // 포인터 bp는 병합된 시작 주소(이전 블록)로 이동
    } else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    return bp; // 병합된 혹은 병합되지 않은 블록의 시작 포인터를 반환함
}

// 힙 공간을 확장할 때 사용한다.
// malloc이 요청한 크기의 블록을 못 찾을 때, 새로운 메모리 공간을 확보하기 위해 호출되는 함수다.
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    // 정렬 단위 맞춰서 크기 계산
    // 메모리는 더블 워드(8바이트) 정렬이 되어야 한다.
    // 홀수 개의 워드가 들어오면, +1 해서 짝수로 만들어 정렬 맞춤
    // 결국 size는 8의 배수임
    // 예:
    // words = 5 -> (5 + 1) * 4 = 24
    // words = 6 -> 6 * 4 = 24
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    // 힙 공간 확장
    // mem_sbrk()는 힙 포인터를 size 만큼 증가시키고, 그 확정된 영역의 시작 주소를 반환함
    // bp: 새 블록의 payload 시작 주소 (즉, header 바로 뒤 주소)
    if ((long)(bp = mem_sbrk(size)) == -1) {
        return NULL;
    }

    // 블록 초기화 (헤더/푸터 설정 + 에필로그)
    // [ Header | Payload .... | Footer ]
    // Header: 블록의 크기 + 할당 여부
    // Payload: 사용자가 쓸 수 있는 데이터 영역
    // Footer: 헤더 정보의 복사본 (경계 태그)
    PUT(HDRP(bp), PACK(size, 0)); // 헤더 - HDRP(bp) -> 헤더 위치 계산(bp - WSIZE) | PACK(size, 0) -> size | 0x0으로 size만 설정, 할당 안됨 표시
    PUT(FTRP(bp), PACK(size, 0)); // 푸터 - FTRP(bp) -> 푸터 위치 계산(bp + size - DSIZE) | PACK(size, 0) -> free 상태 표기
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 새 에필로그 헤더 -> 할당기의 구조에서 항상 마지막 블록 뒤에 에필로그가 있어야 하기 때문이다.

    // 앞쪽 블록이 free일 수 있으니, bp와 인점한 블록들을 병합함
    // 연결된 블록의 시작 주소를 반환 그러면 coalesce()에서 알아서 처리함
    return coalesce(bp);
}

// // asize: 정렬/오버헤드 포함된 요청 크기 (즉, 조정된 블록 크기) = malloc(size) 요청이 들어왔을 때 할당기는 내부에서 요청된 size를 바로 쓰지 않고 메모리 정렬, 헤더/푸터 오버헤드, 최소 블록 크기 등을 고려해서 실제로 할당할 크기를 계산함
// static void *find_fit(size_t asize) {
//     // 현재 검사 중인 블록의 포인터
//     void *bp;

//     // bp = heap_listp: 첫 번째 블록부터 검사 시작
//     // GET_SIZE(HDRP(bp)) > 0: 종료 조건, 에필로그 블록(크기 0)에 도달하면 탐색 종료
//     // bp = NEXT_BLKP(bp) 다음 블록으로 이동하는 매크로
//     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
//         // !GET_ALLOC(...) 이 블록이 free인지 확인하는거임
//         // asize <= GET_SIZE(...) 요청한 크기를 수용할 수 있는 확인하는 거임
//         // 조건이 맞으면 bp 반환 = First Fit 전략
//         if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
//             // 조건이 맞으면 바로 bp 반환 = First fit 전략임
//             return bp;
//         }
//     }

//     // 끝까지 가용 블록을 못 찾으면 NULL 반환
//     // 이 경우 malloc()은 extend_heap()을 호출해서 힙을 늘릴 수 있음
//     return NULL;
// }

// static void *find_fit(size_t asize) {
//     void *bp;
//     void *best_fit = NULL;
//     size_t min_diff = (size_t) - 1;
    
//     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
//         if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
//             size_t diff = GET_SIZE(HDRP(bp)) - asize;
//             if (diff < min_diff) {
//                 min_diff = diff;
//                 best_fit = bp;
//             }
//         }
//     }
    
//     return best_fit;
// }

static void *find_fit(size_t asize) {
    void *bp;
    
    // rover가 초기화되지 않았거나 NULL인 경우, 힙의 시작점부터 검색
    if (rover == NULL || rover == 0) {
        rover = heap_listp;
    }
    
    // 첫 번째 패스: rover 위치부터 힙의 끝까지 검색
    for (bp = rover; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            rover = bp; // 다음 검색을 위해 rover 업데이트
            return bp;
        }
    }
    
    // 두 번째 패스: 힙의 시작부터 rover 위치까지 검색
    for (bp = heap_listp; bp < rover; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            rover = bp; // 다음 검색을 위해 rover 업데이트
            return bp;
        }
    }
    
    // 적합한 블록을 찾지 못한 경우
    return NULL;
}

// 블록을 할당하고, 남는 공간이 충분하면 가용 블록으로 분할하는 역할
// bp: 가용 블록의 포인터 (할당기로부터 찾은 블록 시작 주소)
// asize: 할당하고자 하는 조정된 블록 크기 (payload + header/footer + 정렬 포함)
static void place(void *bp, size_t asize) {
    // 현재 가용 블록의 전체 크기
    size_t csize = GET_SIZE(HDRP(bp)); // 헤더에서 블록 크기를 읽어옴

    // 블록이 너무 커서 나눌 수 있는 경우 (분할) -> 내부 단편화가 발생하는걸 최대한으로 줄이기 위함
    if ((csize - asize) >= (2 * DSIZE)) {
        // 앞 부분은 요청된 크기로 할당 처리함
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        // 다음 블록 위치로 이동
        bp = NEXT_BLKP(bp);
        // 남은 공간을 새로운 사용 블록으로 설정
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    // 분할이 불가능한 경우 그냥 통째로 할당함
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *) - 1) {
        return -1;
    }

    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
    heap_listp += (2 * WSIZE);

    rover = heap_listp;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {
        return -1;
    }

    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0) {
        return NULL;
    }

    if (size <= DSIZE) {
        asize = 2 * DSIZE;
    } else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    // 적당한 가용 블럭이 없으면 힙 영역을 넓혀야함
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    // 사이즈는 블록 전체의 크기다.
    /*
    [ Header | Payload .... | Footer ]
        ^                         ^
        |                         |
        HDRP(ptr)             FTRP(ptr)

        블록 전체 크기 = Header + Payload (+ Padding) + Footer
    */
    size_t size = GET_SIZE(HDRP(ptr));

    // 가용 블럭의 헤더와 푸터를 비운다.
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    // 그러고 앞/뒤 확인하고 케이스에 맞게 가용 블럭을 병합한다.
    void *coalesced_ptr = coalesce(ptr);

    if (coalesced_ptr < rover) {
        rover = coalesced_ptr;
    }
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}