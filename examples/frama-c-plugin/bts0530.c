#include <stdbool.h>
#include <stdint.h>

/* #include <stdio.h> */
#include <stdlib.h>
#include <string.h>

unsigned long long rnd;
uint32_t ext;


static uint64_t __global_clock = 0;



struct {  /* state */
  struct {  /* t3 */
    bool prophVal__b[3];
    int32_t prophVal__a[3];
    bool outputVal__b;
    int32_t outputVal__a;
    int32_t tmpSampleVal__ext_1;
    int32_t tmpSampleVal__ext_8;
  } t3;
} state =
{  /* state */
  {  /* t3 */
    /* prophVal__b */
    { true
    , false
    , false
    },
    /* prophVal__a */
    { 0L
    , 1L
    , 0L
    },
    /* outputVal__b */  false,
    /* outputVal__a */  0L,
    /* tmpSampleVal__ext_1 */  0L,
    /* tmpSampleVal__ext_8 */  0L
  }
};

/* t3.update__b */
static void __r0() {
  bool __0 = true;
  int32_t __1 = 2L;
  uint64_t __2 = 0ULL;
  int32_t __3 = state.t3.prophVal__a[__2];
  int32_t __4 = __1 + __3;
  int32_t __5 = 5L;
  int32_t __6 = state.t3.tmpSampleVal__ext_1;
  int32_t __7 = __5 + __6;
  bool __8 = __4 < __7;
  uint64_t __9 = 2ULL;
  if (__0) {
  }
  state.t3.prophVal__b[__9] = __8;
}

/* t3.update__a */
static void __r3() {
  bool __0 = true;
  uint64_t __1 = 0ULL;
  int32_t __2 = state.t3.prophVal__a[__1];
  int32_t __3 = state.t3.tmpSampleVal__ext_8;
  int32_t __4 = state.t3.tmpSampleVal__ext_1;
  int32_t __5 = __3 + __4;
  int32_t __6 = __3 + __5;
  int32_t __7 = __2 + __6;
  uint64_t __8 = 2ULL;
  if (__0) {
  }
  state.t3.prophVal__a[__8] = __7;
}

/* t3.output__b */
static void __r1() {
  bool __0 = true;
  uint64_t __1 = 0ULL;
  bool __2 = state.t3.prophVal__b[__1];
  if (__0) {
  }
  state.t3.outputVal__b = __2;
}

/* t3.output__a */
static void __r4() {
  bool __0 = true;
  uint64_t __1 = 0ULL;
  int32_t __2 = state.t3.prophVal__a[__1];
  if (__0) {
  }
  state.t3.outputVal__a = __2;
}

/* t3.sample__ext_1 */
static void __r6() {
  bool __0 = true;
  int32_t __1 = ext;
  if (__0) {
  }
  state.t3.tmpSampleVal__ext_1 = __1;
}

/* t3.shiftArr__a */
static void __r5() {
  bool __0 = true;
  uint64_t __1 = 2ULL;
  int32_t __2 = state.t3.prophVal__a[__1];
  uint64_t __3 = 1ULL;
  int32_t __4 = state.t3.prophVal__a[__3];
  uint64_t __5 = 0ULL;
  if (__0) {
  }
  state.t3.prophVal__a[__3] = __2;
  state.t3.prophVal__a[__5] = __4;
}

/* t3.shiftArr__b */
static void __r2() {
  bool __0 = true;
  uint64_t __1 = 2ULL;
  bool __2 = state.t3.prophVal__b[__1];
  uint64_t __3 = 1ULL;
  bool __4 = state.t3.prophVal__b[__3];
  uint64_t __5 = 0ULL;
  if (__0) {
  }
  state.t3.prophVal__b[__3] = __2;
  state.t3.prophVal__b[__5] = __4;
}

/* t3.sample__ext_8 */
static void __r7() {
  bool __0 = true;
  int32_t __1 = ext;
  if (__0) {
  }
  state.t3.tmpSampleVal__ext_8 = __1;
}



void t3() {
  {
    static uint8_t __scheduling_clock = 0;
    if (__scheduling_clock == 0) {
      __r0();  /* t3.update__b */
      __r3();  /* t3.update__a */
      __scheduling_clock = 8;
    }
    else {
      __scheduling_clock = __scheduling_clock - 1;
    }
  }
  {
    static uint8_t __scheduling_clock = 1;
    if (__scheduling_clock == 0) {
      __r1();  /* t3.output__b */
      __r4();  /* t3.output__a */
      __r6();  /* t3.sample__ext_1 */
      __scheduling_clock = 8;
    }
    else {
      __scheduling_clock = __scheduling_clock - 1;
    }
  }
  {
    static uint8_t __scheduling_clock = 2;
    if (__scheduling_clock == 0) {
      __r5();  /* t3.shiftArr__a */
      __scheduling_clock = 8;
    }
    else {
      __scheduling_clock = __scheduling_clock - 1;
    }
  }
  {
    static uint8_t __scheduling_clock = 3;
    if (__scheduling_clock == 0) {
      __r2();  /* t3.shiftArr__b */
      __scheduling_clock = 8;
    }
    else {
      __scheduling_clock = __scheduling_clock - 1;
    }
  }
  {
    static uint8_t __scheduling_clock = 8;
    if (__scheduling_clock == 0) {
      __r7();  /* t3.sample__ext_8 */
      __scheduling_clock = 8;
    }
    else {
      __scheduling_clock = __scheduling_clock - 1;
    }
  }

  __global_clock = __global_clock + 1;

}

int main(int argc, char *argv[]) {
  if (argc != 2) {
    return 1;
  }
  /* rnd = atoi(argv[1]);*/
  rnd = 10;

  state.t3.tmpSampleVal__ext_8 = ext;
  state.t3.tmpSampleVal__ext_1 = ext;
  int i = 0;
  for(; i < rnd ; i++) {
    int j = 0;
    for (; j < 9 ; j++) {
      t3();
    }
/*    printf("period: %i   ", i);
    printf("a: %ld   ", state.t3.outputVal__a);
    printf("b: %hu   ", state.t3.outputVal__b);
    printf("\n" );
    fflush(stdout); */
  }
  return EXIT_SUCCESS;
}

