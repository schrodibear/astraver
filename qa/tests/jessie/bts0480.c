
#include <stdint.h>

// This works.
//int32_t a;

// This doesn't.
volatile int32_t a;

void f(double b) {
  a = (int32_t) b;
}

