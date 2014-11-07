// Should be run with -jessie-specialize

// separated__type is required for memcpy and is
// currently only supported in SeparationPolicy(none) mode
#pragma SeparationPolicy(none)

typedef unsigned long size_t;

struct inner {
  int a, b;
  char c;
  void *p;
};

struct outer {
  struct inner *pinner;
  struct inner inner;
  int a;
  struct inner ainner[5];
  int b;
  char c;
  long long l;
};

// This assigns clause is just a stub to suppress Frama-C warning about
// missing assigns clause.
// Mallocs are always translated to embedded allocation constructs anyway.
//@ assigns \nothing;
extern void *malloc (size_t size);

// kmalloc is translated exactly like malloc
// Hepofully they can't be mixed in the same code (kernel vs. user-space)
//@ assigns \nothing;
extern void *kmalloc (size_t size, int priority);

// This assigns clause is also a stub.
// With option -jessie-specialize the specialized version from jessie_spec_prolog.h is used.
//@ assigns ((char *)dest)[0 .. (n / sizeof (char)) - 1] \from ((char *)src)[0 .. (n / sizeof (char)) - 1];
extern void *memcpy(void *restrict dest, const void *restrict src, size_t n);

// Same thing here.
//@ assigns ((char *)dest)[0 .. (n / sizeof (char)) - 1] \from ((char *)src)[0 .. (n / sizeof (char)) - 1];
extern void *memmove(void *dest, const void *src, size_t n);

// And here.
//@ assigns \nothing;
extern int memcmp(const void *dest, const void *src, size_t n);

//@ assigns ((char *)dest)[0 .. (n / sizeof (char)) - 1];
extern void *memset(void *dest, int val, size_t n);

//@ assigns \nothing;
extern void free(void *ptr);

//@ assigns \nothing;
extern void kfree(void *ptr);

void main(int n)
{
  char *ac1, *ac2;
  struct inner *ain1, *ain2, *ain3, *ain4;
  struct outer *aout1, *aout2;
  int *ai1, *ai2;
  char vc1[400], vc2[400];
  int flag;
  if (n > 6 && n <= 100) {
    ac1 = malloc(sizeof(int) * n);
    ac2 = malloc(sizeof(int) * n);
    ac2 = (char *) memcpy(ac2, ac1, n * sizeof(char));
    //@ assert ac1[0] == ac2[0];
    //@ assert ac1[1] == ac2[1];

    flag = memcmp(&ac1[1], &ac2[1], (n - 1) * sizeof(char));
    //@ assert flag == 0;

    ain1 = kmalloc(sizeof(struct inner) * (n / 2), 0);
    if (!ain1) {
      return;
    }
    ain2 = malloc(sizeof(struct inner) * (n / 2));
    //@ assert \valid(vc1+(0..399)) && \offset_min(vc1) == 0;
    //@ assert \valid(vc2+(0..399)) && \offset_min(vc2) == 0;
    memcpy(ain2, ain1, (n / 2) * (sizeof *ain1));
    //@ assert ain1[0] == ain2[0];
    //@ assert ain1[1].a == ain2[1].a;
    //@ assert ain1[1].c == ain2[1].c;

    // Intermediate assertons that help proving the following (flag == 0) goal
    //@ assert \forall integer i; 0 <= i < n / 2 ==> ain1[i] == ain2[i];
    //@ assert \forall integer i; 0 <= i < n / 3 ==> ain1[i] == ain2[i];
    flag = memcmp(ain1, ain2, (n / 3) * (sizeof *ain1));
    //@ assert flag == 0;

    aout1 = malloc(sizeof(struct outer) * (n / 2));
    aout2 = malloc(sizeof(struct outer) * (n / 2));
    //@ assert \valid(vc1+(0..399)) && \offset_min(vc1) == 0;
    //@ assert \valid(vc2+(0..399)) && \offset_min(vc2) == 0;
    aout2 = (struct s2 *) memcpy(aout2, aout1, (n / 2) * sizeof(struct outer));
    //@ assert aout1[0] == aout2[0];
    //@ assert aout1[1].ainner[2] == aout2[1].ainner[2];
    //@ assert aout1[1].l == aout2[1].l;

    ai1 = malloc(sizeof(int) * n);
    ai2 = malloc(sizeof(int) * n);
    //@ assert \valid(vc1+(0..399)) && \offset_min(vc1) == 0;
    //@ assert \valid(vc2+(0..399)) && \offset_min(vc2) == 0;
    ai2 = memmove(ai2, ai1, n * sizeof(int));
    //@ assert ai1[1] == ai2[1];

    //@ assert ac1[0] == ac2[0];

    memmove(vc1, vc2, n * sizeof(char));
    flag = memcmp(&vc1[1], &vc2[1], (n - 1) * sizeof(char));
    //@ assert flag == 0;
    //@ assert vc1[0] == vc2[0];

    // Another bug in Jessie translation: if we didn't use the following
    // dummy `if' statement, the label L would be propagated upwards by several
    // statements, and can therefore potentially stand before some modification of v2.
    // Seems to be a bug in block folding.
    // Fixed in local version
    L:
    memmove(vc2, &vc2[30], 40 * sizeof(char));
    //@ assert \forall integer i; 0 <= i <= 10 ==> vc2[i] == \at(vc2[i + 30], L);

    flag = memcmp(&vc2[10], &vc2[40], 30 * sizeof(char));
    //@ assert \forall integer i; 0 <= i < 30 ==> vc2[i + 40] == \at(vc2[i + 40], L);
    //@ assert \forall integer i; 0 <= i < 30 ==> vc2[i + 10] == \at(vc2[i + 40], L);
    //@ assert \forall integer i; 0 <= i < 30 ==> vc2[i + 10] == vc2[i + 40];
    //@ assert \forall integer i; &vc2[10] + i == &vc2[i + 10] && &vc2[40] + i == &vc2[i + 40];
    //@ assert \forall integer i; 0 <= i < 30 ==> *(&vc2[10] + i) == *(&vc2[40] + i);
    //@ assert flag == 0;

    memset(ai2, 0, 5 * sizeof(int));
    //@ assert ai2[1] == 0;
    //@ assert ai2[3] == 0;
    //@ assert ai2[4] == 0;

    memset(aout1, 0, 3 * sizeof(struct outer));
    //@ assert aout1[1].ainner[2].p == \null;
    //@ assert aout1[2].l == 0;

    ain3 = kmalloc(sizeof(struct inner) * (n / 2), 0);
    if (!ain3) {
      return;
    }
    ain4 = malloc(sizeof(struct inner) * (n / 2));
    free(ain4);
    kfree(ain3);
   }
}
