
#include <stdint.h>

/*@ requires (r > 0) && (r < 32); */
uint32_t rotate_left (uint32_t x, uint32_t r)
{
  return (x << r) | (x >> (32-r));
} 
