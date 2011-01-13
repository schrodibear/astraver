
typedef unsigned int uint;
typedef struct Heap {
  int x;
} *heap;

//@ assigns \nothing;
extern heap create(uint sz);

//@ assigns u->x;
extern void insert(heap u, int e);

//@ assigns \nothing;
extern int extract_min(heap u);


