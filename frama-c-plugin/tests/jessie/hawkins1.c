#include <stdint.h>

// This works...
uint32_t * a;

// But this throws a type error...
// volatile uint32_t * a;

void f(double b) {
  *a = (uint32_t) b;
}
