

typedef unsigned int size_t;

void * alloc (size_t size);

void *ptr1, *ptr2;

/*@ ensures ptr1 != ptr2
  @*/
void f() {
  ptr1 = alloc(10);
  ptr2 = alloc(10);
}
