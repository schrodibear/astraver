//#include <stddef.h>

//typedef unsigned long size_t;
//@ assigns \nothing;
extern void * kzalloc(size_t size, int flags);
//@ assigns \nothing;
extern void * kmalloc(size_t size, int flags);
//@ assigns \nothing;
void * memset ( void * ptr, int value, size_t num );

int main(void)
{
  int *a, *b;
  b = kmalloc(sizeof(int), 0);
  a = kzalloc(sizeof(int) * 25, 0);
  kzalloc(sizeof(int) * 4, 0);
}
